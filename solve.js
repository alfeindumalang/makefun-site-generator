// A fast, byte-exact reimplementation of makefun-site 1.0.0's build().
// It returns the same output tree for every input, using less CPU.
//
// The speed comes from doing less work, never from different answers:
//  - inline Markdown escapes plain-text runs in one regex pass instead of
//    one escapeHtml() call per character (the reference's hottest spot);
//  - the block lexer dispatches on the first character of each line instead
//    of testing seven regexes per line, and trims are index scans;
//  - slugify() skips NFKD + combining-mark removal for ASCII-only text (an
//    identity there) and its results are memoised per case, since titles
//    and tag names repeat constantly;
//  - front matter is scanned by line boundaries with indexOf, so the body
//    stays a substring instead of a split-and-rejoin of the whole file;
//  - template rendering memoises includes whose output depends only on
//    case-constant values or on one loop element, so the header and every
//    post card are rendered once per case, not once per page;
//  - every cache is created fresh inside run(): nothing carries from one
//    case to the next. No clock, no environment, no randomness.

const REPORT_FILE = 'build-report.txt';
const RESERVED = Object.freeze(['posts', 'tags', 'page']);
const INCLUDE_DEPTH = 8;

/** Code-unit order (never locale order). */
const byCodeUnits = (a, b) => (a < b ? -1 : a > b ? 1 : 0);

// ------------------------------------------------------------------ text

const ESCAPES = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };
const NEEDS_ESCAPE = /[&<>"']/;

/** `text` with & < > " ' escaped; returned unchanged when none occur. */
function escapeHtml(text) {
  return NEEDS_ESCAPE.test(text) ? text.replace(/[&<>"']/g, (ch) => ESCAPES[ch]) : text;
}

const SLUG_MAX = 64;
const MONTHS = ['January', 'February', 'March', 'April', 'May', 'June', 'July', 'August', 'September', 'October', 'November', 'December'];

/**
 * The slug of `text`, uncached (see slugify): NFKD, combining marks
 * dropped, A-Z lowered, every run of other characters one '-', none at
 * either end, at most 64 characters, 'untitled' when nothing is left.
 * NFKD + mark removal is the identity on ASCII-only text, so that step is
 * skipped when no code unit is above 127.
 */
function slugifyUncached(text) {
  let plain = text;
  let allAscii = true;
  for (let i = 0; i < text.length; i++) {
    if (text.charCodeAt(i) > 127) {
      allAscii = false;
      break;
    }
  }
  if (!allAscii) plain = text.normalize('NFKD').replace(/\p{M}/gu, '');
  let out = '';
  let pendingDash = false;
  for (let i = 0; i < plain.length; i++) {
    const c = plain.charCodeAt(i);
    let keep = -1;
    if (c >= 65 && c <= 90) keep = c + 32;
    else if ((c >= 97 && c <= 122) || (c >= 48 && c <= 57)) keep = c;
    if (keep < 0) {
      if (out.length > 0) pendingDash = true;
      continue;
    }
    if (pendingDash) out += '-';
    pendingDash = false;
    out += String.fromCharCode(keep);
  }
  out = out.slice(0, SLUG_MAX).replace(/-+$/, '');
  return out === '' ? 'untitled' : out;
}

/** Per-case slug cache; slugify is pure and titles/tag names repeat. */
let slugCache = null;
function slugify(text) {
  let v = slugCache.get(text);
  if (v === undefined) {
    v = slugifyUncached(text);
    slugCache.set(text, v);
  }
  return v;
}

/** `slug` made unique against `taken` (and added to it). */
function uniqueSlug(slug, taken) {
  let out = slug;
  for (let n = 2; taken.has(out); n++) out = `${slug}-${n}`;
  taken.add(out);
  return out;
}

/** A YYYY-MM-DD date in words, from the string alone. */
function longDate(date) {
  return `${Number(date.slice(8, 10))} ${MONTHS[Number(date.slice(5, 7)) - 1]} ${date.slice(0, 4)}`;
}

/** Whether code unit `c` is one of JavaScript's \s characters. */
function isWhitespace(c) {
  return (
    c === 32 || c === 9 || c === 10 || c === 11 || c === 12 || c === 13 ||
    c === 0x00a0 || c === 0x1680 || (c >= 0x2000 && c <= 0x200a) ||
    c === 0x2028 || c === 0x2029 || c === 0x202f || c === 0x205f || c === 0x3000 || c === 0xfeff
  );
}

/** The words of a body: its runs of characters other than whitespace. */
function wordsOf(text) {
  let count = 0;
  let inWord = false;
  for (let i = 0; i < text.length; i++) {
    if (isWhitespace(text.charCodeAt(i))) inWord = false;
    else if (!inWord) {
      inWord = true;
      count++;
    }
  }
  return count;
}

/** Spaces and tabs at either end dropped. */
function trimSpacesTabs(line) {
  let start = 0;
  let end = line.length;
  while (start < end && (line.charCodeAt(start) === 32 || line.charCodeAt(start) === 9)) start++;
  while (end > start && (line.charCodeAt(end - 1) === 32 || line.charCodeAt(end - 1) === 9)) end--;
  return start === 0 && end === line.length ? line : line.slice(start, end);
}

/** Whether a line holds only spaces and tabs. */
function isBlankLine(line) {
  for (let i = 0; i < line.length; i++) {
    const c = line.charCodeAt(i);
    if (c !== 32 && c !== 9) return false;
  }
  return true;
}

// ---------------------------------------------------------- front matter

const KEYS = Object.freeze(['title', 'date', 'tags', 'draft', 'layout', 'slug', 'summary']);
const KEY_VALUE = /^([a-z_]+):(?: (.*))?$/;
const DATE_RE = /^(\d{4})-(\d{2})-(\d{2})$/;
const TEMPLATE_NAME = /^[a-z0-9-]+$/;
const SLUG_RE = /^[a-z0-9]+(?:-[a-z0-9]+)*$/;
const TAG_RE = /^[^"[\]]+$/;

/** The days of month `m` (1-12) of year `y`, by the Gregorian rule. */
function daysInMonth(y, m) {
  if (m === 2) return (y % 4 === 0 && y % 100 !== 0) || y % 400 === 0 ? 29 : 28;
  return [4, 6, 9, 11].includes(m) ? 30 : 31;
}

/** A string value: "..." with \" and \\ its only escapes, or a bare value. */
function stringValue(raw) {
  if (raw.startsWith('"')) {
    if (raw.length < 2 || !raw.endsWith('"')) return { error: 'a quoted string is not closed' };
    let out = '';
    for (let i = 1; i < raw.length - 1; i++) {
      const c = raw[i];
      if (c === '\\') {
        const n = raw[i + 1];
        if ((n !== '"' && n !== '\\') || i + 1 === raw.length - 1) {
          return { error: 'a quoted string holds an escape other than \\" or \\\\' };
        }
        out += n;
        i++;
      } else if (c === '"') {
        return { error: 'a quoted string holds a stray quote' };
      } else {
        out += c;
      }
    }
    return { value: out };
  }
  if (raw.startsWith('[')) return { error: 'a bare string opens on [' };
  return { value: raw };
}

/** One key's value, or why it is refused. */
function keyValue(key, raw) {
  switch (key) {
    case 'title':
    case 'summary': {
      const s = stringValue(raw);
      return 'error' in s ? { error: `key "${key}": ${s.error}` } : s;
    }
    case 'date': {
      const m = DATE_RE.exec(raw);
      const y = m ? Number(m[1]) : 0;
      const mo = m ? Number(m[2]) : 0;
      const d = m ? Number(m[3]) : 0;
      if (!m || y < 1970 || y > 2099 || mo < 1 || mo > 12 || d < 1 || d > daysInMonth(y, mo)) {
        return { error: 'key "date": not a date from 1970-01-01 to 2099-12-31 (YYYY-MM-DD)' };
      }
      return { value: raw };
    }
    case 'tags': {
      if (!raw.startsWith('[') || !raw.endsWith(']')) return { error: 'key "tags": not a list [a, b]' };
      const inner = raw.slice(1, -1);
      if (inner.trim() === '') return { value: [] };
      const tags = inner.split(',').map((t) => t.trim());
      if (tags.some((t) => t === '' || !TAG_RE.test(t))) {
        return { error: 'key "tags": an empty tag, or one holding " [ or ]' };
      }
      return { value: tags };
    }
    case 'draft':
      return raw === 'true' ? { value: true } : raw === 'false' ? { value: false } : { error: 'key "draft": true or false' };
    case 'layout':
      return TEMPLATE_NAME.test(raw) ? { value: raw } : { error: 'key "layout": not a template name' };
    case 'slug':
      return SLUG_RE.test(raw) && raw.length <= 64 ? { value: raw } : { error: 'key "slug": not a slug' };
    default:
      return { error: `unknown key "${key}"` };
  }
}

/**
 * A source's front matter and body: { data, body }, or { error } with the
 * first reason it is refused. Line boundaries are scanned with indexOf, so
 * the body is a substring of `text` (the reference splits the whole file
 * and joins the body back: the same text either way).
 */
function parseFrontMatter(text) {
  const firstNl = text.indexOf('\n');
  const first = firstNl === -1 ? text : text.slice(0, firstNl);
  if (first !== '---') return { error: 'no front matter' };
  // Locate the closing --- line: its 0-based line number and where the body starts.
  let pos = firstNl === -1 ? text.length : firstNl + 1;
  let lineNo = 1;
  let closeLine = -1;
  let bodyStart = -1;
  while (pos <= text.length) {
    const eol = text.indexOf('\n', pos);
    const lineEnd = eol === -1 ? text.length : eol;
    if (text.slice(pos, lineEnd) === '---') {
      closeLine = lineNo;
      bodyStart = eol === -1 ? text.length : eol + 1;
      break;
    }
    if (eol === -1) break;
    pos = lineEnd + 1;
    lineNo++;
  }
  if (closeLine === -1) return { error: 'the front matter is not closed' };
  const data = {};
  pos = firstNl === -1 ? text.length : firstNl + 1;
  for (let i = 1; i < closeLine; i++) {
    const eol = text.indexOf('\n', pos);
    const lineEnd = eol === -1 ? text.length : eol;
    const line = text.slice(pos, lineEnd);
    if (/^[ \t]*$/.test(line) || line.startsWith('#')) {
      pos = lineEnd + 1;
      continue;
    }
    const m = KEY_VALUE.exec(line);
    if (!m) return { error: `line ${i + 1} is not "key: value"` };
    const key = m[1];
    const raw = (m[2] ?? '').replace(/[ \t]+$/, '');
    if (!KEYS.includes(key)) return { error: `unknown key "${key}"` };
    if (Object.hasOwn(data, key)) return { error: `key "${key}" is given twice` };
    if (raw === '') return { error: `key "${key}" has no value` };
    const v = keyValue(key, raw);
    if ('error' in v) return v;
    data[key] = v.value;
    pos = lineEnd + 1;
  }
  if (!Object.hasOwn(data, 'title')) return { error: 'no title' };
  return { data, body: text.slice(bodyStart) };
}

// -------------------------------------------------------------- markdown

/** Fence opener: its language, or null (``` + language + spaces/tabs). */
function fenceLanguage(line) {
  if (line.charCodeAt(0) !== 96 || line.charCodeAt(1) !== 96 || line.charCodeAt(2) !== 96) return null;
  let i = 3;
  while (i < line.length) {
    const c = line.charCodeAt(i);
    if ((c >= 65 && c <= 90) || (c >= 97 && c <= 122) || (c >= 48 && c <= 57) || c === 95 || c === 43 || c === 45) i++;
    else break;
  }
  const lang = line.slice(3, i);
  while (i < line.length) {
    const c = line.charCodeAt(i);
    if (c !== 32 && c !== 9) return null;
    i++;
  }
  return lang;
}

/** Fence closer: ``` then spaces or tabs only. */
function isFenceCloser(line) {
  if (line.charCodeAt(0) !== 96 || line.charCodeAt(1) !== 96 || line.charCodeAt(2) !== 96) return false;
  for (let i = 3; i < line.length; i++) {
    const c = line.charCodeAt(i);
    if (c !== 32 && c !== 9) return false;
  }
  return true;
}

/** A heading line's level and text, or null (text never empty, at most 6 #). */
function headingOf(line) {
  let hashes = 0;
  while (hashes < line.length && line.charCodeAt(hashes) === 35) hashes++;
  if (hashes === 0 || hashes > 6 || hashes >= line.length) return null;
  const after = line.charCodeAt(hashes);
  if (after !== 32 && after !== 9) return null;
  let start = hashes + 1;
  while (start < line.length && (line.charCodeAt(start) === 32 || line.charCodeAt(start) === 9)) start++;
  let end = line.length;
  while (end > start && (line.charCodeAt(end - 1) === 32 || line.charCodeAt(end - 1) === 9)) end--;
  if (end === start) return null;
  return { depth: hashes, text: line.slice(start, end) };
}

/** Thematic break: --- or *** then spaces or tabs only. */
function isThematicBreak(line) {
  const first = line.charCodeAt(0);
  if (first !== 45 && first !== 42) return false;
  if (line.charCodeAt(1) !== first || line.charCodeAt(2) !== first) return false;
  for (let i = 3; i < line.length; i++) {
    const c = line.charCodeAt(i);
    if (c !== 32 && c !== 9) return false;
  }
  return true;
}

/** A bullet item's text, or null. */
function bulletText(line) {
  const c0 = line.charCodeAt(0);
  if ((c0 === 45 || c0 === 42) && line.charCodeAt(1) === 32) return line.slice(2);
  return null;
}

/** An ordered item: { start, text }, or null (1-9 digits, ". "). */
function orderedItem(line) {
  let digits = 0;
  while (digits < 9 && digits < line.length) {
    const c = line.charCodeAt(digits);
    if (c < 48 || c > 57) break;
    digits++;
  }
  if (digits === 0) return null;
  if (line.charCodeAt(digits) !== 46 || line.charCodeAt(digits + 1) !== 32) return null;
  return { start: Number(line.slice(0, digits)), text: line.slice(digits + 2) };
}

/** A list continuation: two or more spaces, then a non-space character. */
function isContinuation(line) {
  let spaces = 0;
  while (spaces < line.length && line.charCodeAt(spaces) === 32) spaces++;
  return spaces >= 2 && spaces < line.length && !isWhitespace(line.charCodeAt(spaces));
}

/** Whether `line` ends a paragraph: blank, fence, heading or break. */
function endsParagraph(line) {
  if (line.length === 0) return true;
  const c0 = line.charCodeAt(0);
  if (c0 === 32 || c0 === 9) return isBlankLine(line);
  if (c0 === 96) return fenceLanguage(line) !== null;
  if (c0 === 35) return headingOf(line) !== null;
  if (c0 === 45 || c0 === 42) return isThematicBreak(line);
  return false;
}

/** Read one list starting at `i`; push its token and return the next index. */
function readList(lines, i, ordered, start, tokens) {
  const items = [];
  const n = lines.length;
  while (i < n) {
    const l = lines[i];
    if (ordered) {
      const m = orderedItem(l);
      if (m !== null) {
        items.push([trimSpacesTabs(m.text)]);
        i++;
        continue;
      }
    } else {
      const m = bulletText(l);
      if (m !== null) {
        items.push([trimSpacesTabs(m)]);
        i++;
        continue;
      }
    }
    if (isContinuation(l)) {
      items[items.length - 1].push(trimSpacesTabs(l));
      i++;
      continue;
    }
    break;
  }
  tokens.push({ type: 'list', ordered, start, items: items.map((parts) => parts.join('\n')) });
  return i;
}

/** `src`'s block tokens, in order. Dispatches on the first character. */
function lex(src) {
  const lines = src.split('\n');
  const tokens = [];
  let i = 0;
  const n = lines.length;
  while (i < n) {
    const line = lines[i];
    const c0 = line.length === 0 ? -1 : line.charCodeAt(0);
    if (c0 === -1 || c0 === 32 || c0 === 9) {
      if (isBlankLine(line)) {
        i++;
        continue;
      }
    } else if (c0 === 96) {
      const lang = fenceLanguage(line);
      if (lang !== null) {
        const body = [];
        i++;
        while (i < n && !isFenceCloser(lines[i])) body.push(lines[i++]);
        i++;
        tokens.push({ type: 'code', lang, lines: body });
        continue;
      }
    } else if (c0 === 35) {
      const h = headingOf(line);
      if (h !== null) {
        tokens.push({ type: 'heading', depth: h.depth, text: h.text });
        i++;
        continue;
      }
    } else if (c0 === 45 || c0 === 42) {
      if (isThematicBreak(line)) {
        tokens.push({ type: 'hr' });
        i++;
        continue;
      }
      const b = bulletText(line);
      if (b !== null) {
        i = readList(lines, i, false, 1, tokens);
        continue;
      }
    } else if (c0 === 62) {
      const body = [];
      while (i < n && lines[i].charCodeAt(0) === 62) {
        const l = lines[i++];
        body.push(l.length > 1 && l.charCodeAt(1) === 32 ? l.slice(2) : l.slice(1));
      }
      const cleaned = [];
      for (const l of body) {
        const t = trimSpacesTabs(l);
        if (t !== '') cleaned.push(t);
      }
      tokens.push({ type: 'blockquote', lines: cleaned });
      continue;
    } else if (c0 >= 48 && c0 <= 57) {
      const o = orderedItem(line);
      if (o !== null) {
        i = readList(lines, i, true, o.start, tokens);
        continue;
      }
    }
    const body = [trimSpacesTabs(line)];
    i++;
    while (i < n && !endsParagraph(lines[i])) body.push(trimSpacesTabs(lines[i++]));
    tokens.push({ type: 'paragraph', text: body.join('\n') });
  }
  return tokens;
}

/** The characters a backslash escapes. */
const ESCAPABLE = new Set(['\\', '`', '*', '_', '[', ']', '(', ')', '#', '+', '-', '.', '!', '>']);

/** The first index from `from` where `s` holds `what` outside an escape, or -1. */
function findUnescaped(s, what, from) {
  for (let j = from; j <= s.length - what.length; j++) {
    if (s[j] === '\\' && j + 1 < s.length && ESCAPABLE.has(s[j + 1])) {
      j++;
      continue;
    }
    if (s.startsWith(what, j)) return j;
  }
  return -1;
}

/** The first single * from `from` (one whose run is not **), outside an escape, or -1. */
function findSingleStar(s, from) {
  for (let j = from; j < s.length; j++) {
    const c = s[j];
    if (c === '\\' && j + 1 < s.length && ESCAPABLE.has(s[j + 1])) {
      j++;
      continue;
    }
    if (c !== '*') continue;
    if (s[j + 1] === '*') {
      j++;
      continue;
    }
    return j;
  }
  return -1;
}

/**
 * `s` rendered inline; `env.link(target)` resolves a link's href.
 * Same control flow as the reference, but plain-text runs are escaped in
 * one pass instead of one escapeHtml() call per character.
 */
function inline(s, env) {
  let out = '';
  let i = 0;
  const n = s.length;
  while (i < n) {
    const c = s[i];
    if (c === '\\') {
      if (i + 1 < n && ESCAPABLE.has(s[i + 1])) {
        out += escapeHtml(s[i + 1]);
        i += 2;
      } else {
        out += '\\';
        i++;
      }
      continue;
    }
    if (c === '`') {
      const j = s.indexOf('`', i + 1);
      if (j > i + 1) {
        out += `<code>${escapeHtml(s.slice(i + 1, j))}</code>`;
        i = j + 1;
      } else {
        out += '`';
        i++;
      }
      continue;
    }
    if (c === '*') {
      if (s[i + 1] === '*') {
        const j = findUnescaped(s, '**', i + 2);
        if (j > i + 2) {
          out += `<strong>${inline(s.slice(i + 2, j), env)}</strong>`;
          i = j + 2;
        } else {
          out += '**';
          i += 2;
        }
        continue;
      }
      const j = findSingleStar(s, i + 1);
      if (j > i + 1) {
        out += `<em>${inline(s.slice(i + 1, j), env)}</em>`;
        i = j + 1;
      } else {
        out += '*';
        i++;
      }
      continue;
    }
    if (c === '[') {
      const k = findUnescaped(s, ']', i + 1);
      const m = k !== -1 && s[k + 1] === '(' ? s.indexOf(')', k + 2) : -1;
      const target = m === -1 ? '' : s.slice(k + 2, m);
      if (target !== '' && !/\s/.test(target)) {
        out += `<a href="${escapeHtml(env.link(target))}">${inline(s.slice(i + 1, k), env)}</a>`;
        i = m + 1;
        continue;
      }
      out += '[';
      i++;
      continue;
    }
    let j = i;
    while (j < n) {
      const ch = s[j];
      if (ch === '\\' || ch === '`' || ch === '*' || ch === '[') break;
      j++;
    }
    out += escapeHtml(s.slice(i, j));
    i = j;
  }
  return out;
}

/** `src` rendered: its HTML, its table of contents and its excerpt. */
function renderMarkdown(src, env) {
  const ids = new Set();
  const blocks = [];
  const toc = [];
  let excerpt = null;
  for (const t of lex(src)) {
    switch (t.type) {
      case 'heading': {
        const id = uniqueSlug(slugify(t.text), ids);
        const html = inline(t.text, env);
        blocks.push(`<h${t.depth} id="${id}">${html}</h${t.depth}>`);
        if (t.depth === 2 || t.depth === 3) toc.push({ level: t.depth, id, html });
        break;
      }
      case 'code': {
        const cls = t.lang === '' ? '' : ` class="language-${escapeHtml(t.lang)}"`;
        blocks.push(`<pre><code${cls}>${t.lines.map((l) => `${escapeHtml(l)}\n`).join('')}</code></pre>`);
        break;
      }
      case 'hr':
        blocks.push('<hr>');
        break;
      case 'blockquote':
        blocks.push(t.lines.length === 0 ? '<blockquote>\n</blockquote>' : `<blockquote>\n<p>${inline(t.lines.join('\n'), env)}</p>\n</blockquote>`);
        break;
      case 'list': {
        const tag = t.ordered ? 'ol' : 'ul';
        const open = t.ordered && t.start !== 1 ? `<ol start="${t.start}">` : `<${tag}>`;
        blocks.push(`${open}\n${t.items.map((item) => `<li>${inline(item, env)}</li>\n`).join('')}</${tag}>`);
        break;
      }
      case 'paragraph': {
        const html = inline(t.text, env);
        if (excerpt === null) excerpt = html;
        blocks.push(`<p>${html}</p>`);
        break;
      }
    }
  }
  return { html: blocks.map((b) => `${b}\n`).join(''), toc, excerpt: excerpt ?? '' };
}

// ------------------------------------------------------------- templates

const PATH_RE = /^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/;
const FOR_RE = /^for ([A-Za-z_][A-Za-z0-9_]*) in (\S+)$/;
const IF_RE = /^if (not )?(\S+)$/;
const INCLUDE_RE = /^include "([a-z0-9-]+)"$/;

class TemplateError extends Error {}

/** The path `text` names, split at its dots, or a TemplateError. */
function pathOf(name, text) {
  if (!PATH_RE.test(text)) throw new TemplateError(`template "${name}": ${JSON.stringify(text)} is not a path`);
  return text.split('.');
}

/** `src`'s tokens: text, {{ }}, {{{ }}} and {% %}; a standalone tag takes its line. */
function tokenize(name, src) {
  const tokens = [];
  let text = '';
  let i = 0;
  while (i < src.length) {
    const open = src.indexOf('{', i);
    if (open === -1 || open === src.length - 1) {
      text += src.slice(i);
      break;
    }
    const next = src[open + 1];
    if (next !== '{' && next !== '%') {
      text += src.slice(i, open + 1);
      i = open + 1;
      continue;
    }
    text += src.slice(i, open);
    if (next === '{') {
      const raw = src[open + 2] === '{';
      const close = src.indexOf(raw ? '}}}' : '}}', open + (raw ? 3 : 2));
      if (close === -1) throw new TemplateError(`template "${name}": a ${raw ? '{{{' : '{{'} is not closed`);
      if (text !== '') tokens.push({ t: 'text', text });
      text = '';
      tokens.push({ t: raw ? 'raw' : 'var', path: pathOf(name, src.slice(open + (raw ? 3 : 2), close).trim()) });
      i = close + (raw ? 3 : 2);
      continue;
    }
    const close = src.indexOf('%}', open + 2);
    if (close === -1) throw new TemplateError(`template "${name}": a {% is not closed`);
    const end = close + 2;
    const lineStart = src.lastIndexOf('\n', open - 1) + 1;
    const nl = src.indexOf('\n', end);
    const lineEnd = nl === -1 ? src.length : nl;
    const standalone = /^[ \t]*$/.test(src.slice(lineStart, open)) && /^[ \t]*$/.test(src.slice(end, lineEnd));
    if (standalone) text = text.slice(0, text.length - (open - lineStart));
    if (text !== '') tokens.push({ t: 'text', text });
    text = '';
    tokens.push({ t: 'tag', tag: src.slice(open + 2, close).trim() });
    i = standalone ? (nl === -1 ? src.length : nl + 1) : end;
  }
  if (text !== '') tokens.push({ t: 'text', text });
  return tokens;
}

/** `src` parsed into its tree of nodes (a TemplateError when it does not parse). */
function parseTemplate(name, src) {
  const root = { kind: 'root', body: [] };
  const stack = [root];
  let body = root.body;
  for (const tok of tokenize(name, src)) {
    if (tok.t === 'text') body.push({ kind: 'text', text: tok.text });
    else if (tok.t === 'var' || tok.t === 'raw') body.push({ kind: tok.t, path: tok.path });
    else {
      const tag = tok.tag;
      const top = stack[stack.length - 1];
      let m;
      if ((m = FOR_RE.exec(tag)) !== null) {
        const node = { kind: 'for', name: m[1], path: pathOf(name, m[2]), body: [] };
        body.push(node);
        stack.push(node);
        body = node.body;
      } else if ((m = IF_RE.exec(tag)) !== null) {
        const node = { kind: 'if', not: m[1] !== undefined, path: pathOf(name, m[2]), then: [], else: null };
        body.push(node);
        stack.push(node);
        body = node.then;
      } else if (tag === 'else') {
        if (top.kind !== 'if' || top.else !== null) throw new TemplateError(`template "${name}": an else outside an if`);
        top.else = [];
        body = top.else;
      } else if (tag === 'endfor' || tag === 'endif') {
        if (top.kind !== (tag === 'endfor' ? 'for' : 'if')) {
          throw new TemplateError(`template "${name}": an ${tag} with no open ${tag.slice(3)}`);
        }
        stack.pop();
        const parent = stack[stack.length - 1];
        body = parent.kind === 'root' ? parent.body : parent.kind === 'for' ? parent.body : parent.else ?? parent.then;
      } else if ((m = INCLUDE_RE.exec(tag)) !== null) body.push({ kind: 'include', name: m[1] });
      else throw new TemplateError(`template "${name}": {% ${tag} %} is not a tag`);
    }
  }
  if (stack.length > 1) throw new TemplateError(`template "${name}": a ${stack[stack.length - 1].kind} is not closed`);
  return root.body;
}

/** The value at `path` in the scope chain: first name from the nearest scope holding it. */
function lookup(scope, path) {
  let s = scope;
  while (s !== null && !Object.hasOwn(s.vars, path[0])) s = s.parent;
  if (s === null) return undefined;
  let v = s.vars[path[0]];
  for (let k = 1; k < path.length; k++) {
    if (v === null || typeof v !== 'object' || !Object.hasOwn(v, path[k])) return undefined;
    v = v[path[k]];
  }
  return v;
}

/** A value as text: string itself, number in JS digits, true/false, array joined by ", ", else "". */
function textOf(v) {
  if (typeof v === 'string') return v;
  if (typeof v === 'number') return String(v);
  if (typeof v === 'boolean') return v ? 'true' : 'false';
  if (Array.isArray(v)) return v.map(textOf).join(', ');
  return '';
}

/** Whether a value counts as true in an if. */
function truthy(v) {
  if (Array.isArray(v)) return v.length > 0;
  return v !== undefined && v !== null && v !== false && v !== '' && v !== 0;
}

// --- template analysis for memoisation ---------------------------------
// For each template: the first names it reads from its render scope
// (loop-bound names excluded) and its deepest include chain. null when an
// include cycle makes the analysis unusable (then it is never memoised).
// Names in CONST_NAMES are identical for every render of a case.

const CONST_NAMES = new Set(['site', 'tags', 'recent']);
const NO_BOUND = new Set();

function addAll(dst, src) {
  for (const x of src) dst.add(x);
}

function analyzeNodes(nodes, bound, templates, memo, stack) {
  const freeNames = new Set();
  let maxDepth = 0;
  for (const n of nodes) {
    if (n.kind === 'var' || n.kind === 'raw') {
      if (!bound.has(n.path[0])) freeNames.add(n.path[0]);
    } else if (n.kind === 'if') {
      if (!bound.has(n.path[0])) freeNames.add(n.path[0]);
      let r = analyzeNodes(n.then, bound, templates, memo, stack);
      if (r === null) return null;
      addAll(freeNames, r.freeNames);
      maxDepth = Math.max(maxDepth, r.maxDepth);
      if (n.else !== null) {
        r = analyzeNodes(n.else, bound, templates, memo, stack);
        if (r === null) return null;
        addAll(freeNames, r.freeNames);
        maxDepth = Math.max(maxDepth, r.maxDepth);
      }
    } else if (n.kind === 'for') {
      if (!bound.has(n.path[0])) freeNames.add(n.path[0]);
      const inner = new Set(bound);
      inner.add(n.name);
      inner.add('loop');
      const r = analyzeNodes(n.body, inner, templates, memo, stack);
      if (r === null) return null;
      addAll(freeNames, r.freeNames);
      maxDepth = Math.max(maxDepth, r.maxDepth);
    } else if (n.kind === 'include') {
      const sub = templates.get(n.name);
      if (sub === undefined) continue;
      let r;
      if (bound.size === 0) {
        r = analyzeTemplate(n.name, sub, templates, memo, stack);
      } else {
        if (stack.has(n.name)) return null;
        stack.add(n.name);
        r = analyzeNodes(sub, bound, templates, memo, stack);
        stack.delete(n.name);
      }
      if (r === null) return null;
      addAll(freeNames, r.freeNames);
      maxDepth = Math.max(maxDepth, 1 + r.maxDepth);
    }
  }
  return { freeNames, maxDepth };
}

function analyzeTemplate(name, nodes, templates, memo, stack) {
  const hit = memo.get(name);
  if (hit !== undefined) return hit;
  if (stack.has(name)) return null;
  stack.add(name);
  const r = analyzeNodes(nodes, NO_BOUND, templates, memo, stack);
  stack.delete(name);
  memo.set(name, r);
  return r;
}

// --- memo store (nested Maps, LEAF holds the rendered string) -----------

const LEAF = Symbol('leaf');
function memoGet(memo, name, keys) {
  let m = memo.get(name);
  if (m === undefined) return undefined;
  for (const k of keys) {
    m = m.get(k);
    if (m === undefined) return undefined;
  }
  const v = m.get(LEAF);
  return v === undefined ? undefined : v;
}
function memoSet(memo, name, keys, value) {
  let m = memo.get(name);
  if (m === undefined) {
    m = new Map();
    memo.set(name, m);
  }
  for (const k of keys) {
    let next = m.get(k);
    if (next === undefined) {
      next = new Map();
      m.set(k, next);
    }
    m = next;
  }
  m.set(LEAF, value);
}

/**
 * `nodes` rendered in `scope` ({ vars, parent }). `ctx` holds the parsed
 * templates, the HTML escape, the per-template analysis and the memo stores.
 * A for-scope carries isLoop/loopName so the memo logic can tell which
 * names an include's output can depend on. Memoisation is exact: a template
 * is only reused when its free names are provably covered by the cache key,
 * and only when the include-depth arithmetic shows the cached render is
 * complete (no include inside it was cut off by the depth limit).
 */
function renderNodes(nodes, scope, ctx, depth) {
  let out = '';
  for (const n of nodes) {
    switch (n.kind) {
      case 'text':
        out += n.text;
        break;
      case 'var':
        out += ctx.escape(textOf(lookup(scope, n.path)));
        break;
      case 'raw':
        out += textOf(lookup(scope, n.path));
        break;
      case 'if': {
        const v = truthy(lookup(scope, n.path));
        const branch = v !== n.not ? n.then : n.else;
        if (branch !== null) out += renderNodes(branch, scope, ctx, depth);
        break;
      }
      case 'for': {
        const xs = lookup(scope, n.path);
        if (!Array.isArray(xs)) break;
        const body = n.body;
        let fast = null;
        if (body.length === 1 && body[0].kind === 'include' && depth < INCLUDE_DEPTH) {
          const inc = body[0];
          const t = ctx.templates.get(inc.name);
          const an = t !== undefined ? ctx.analysis.get(inc.name) : undefined;
          if (t !== undefined && an !== undefined && an !== null && depth + 1 + an.maxDepth <= INCLUDE_DEPTH) {
            let ok = true;
            for (const f of an.freeNames) {
              if (f !== n.name && f !== 'loop' && !CONST_NAMES.has(f)) {
                ok = false;
                break;
              }
            }
            if (ok) fast = { t, useLoop: an.freeNames.has('loop') };
          }
        }
        if (fast !== null) {
          xs.forEach((x, k) => {
            const loop = { index: k + 1, first: k === 0, last: k === xs.length - 1, length: xs.length };
            const key = fast.useLoop ? [x, loop] : [x];
            let s = memoGet(ctx.memo, body[0].name, key);
            if (s === undefined) {
              s = renderNodes(fast.t, { vars: { [n.name]: x, loop }, parent: scope, isLoop: true, loopName: n.name }, ctx, depth + 1);
              memoSet(ctx.memo, body[0].name, key, s);
            }
            out += s;
          });
        } else {
          xs.forEach((x, k) => {
            const vars = { [n.name]: x, loop: { index: k + 1, first: k === 0, last: k === xs.length - 1, length: xs.length } };
            out += renderNodes(n.body, { vars, parent: scope, isLoop: true, loopName: n.name }, ctx, depth);
          });
        }
        break;
      }
      case 'include': {
        const t = ctx.templates.get(n.name);
        if (t !== undefined && depth < INCLUDE_DEPTH) {
          const an = ctx.analysis.get(n.name);
          if (an !== undefined && an !== null && depth + 1 + an.maxDepth <= INCLUDE_DEPTH) {
            const boundVals = new Map();
            let s = scope;
            while (s !== null) {
              if (s.isLoop) {
                if (!boundVals.has(s.loopName)) boundVals.set(s.loopName, s.vars[s.loopName]);
                if (!boundVals.has('loop')) boundVals.set('loop', s.vars.loop);
              }
              s = s.parent;
            }
            let ok = true;
            const keys = [];
            for (const f of an.freeNames) {
              if (CONST_NAMES.has(f)) continue;
              if (boundVals.has(f)) {
                keys.push(boundVals.get(f));
                continue;
              }
              ok = false;
              break;
            }
            if (ok) {
              if (keys.length === 0) {
                let cached = ctx.memoConst.get(n.name);
                if (cached === undefined) {
                  cached = renderNodes(t, scope, ctx, depth + 1);
                  ctx.memoConst.set(n.name, cached);
                }
                out += cached;
              } else {
                let cached = memoGet(ctx.memo, n.name, keys);
                if (cached === undefined) {
                  cached = renderNodes(t, scope, ctx, depth + 1);
                  memoSet(ctx.memo, n.name, keys, cached);
                }
                out += cached;
              }
              break;
            }
          }
          out += renderNodes(t, scope, ctx, depth + 1);
        }
        break;
      }
    }
  }
  return out;
}

// ------------------------------------------------------------------ build

/** `rel` (a link's path) resolved from the directory `dir`, or null when it climbs out. */
function resolvePath(dir, rel) {
  const parts = dir === '' ? [] : dir.split('/');
  for (const seg of rel.split('/')) {
    if (seg === '' || seg === '.') continue;
    if (seg === '..') {
      if (parts.length === 0) return null;
      parts.pop();
    } else parts.push(seg);
  }
  return parts.join('/');
}

const dirOf = (path) => (path.includes('/') ? path.slice(0, path.lastIndexOf('/')) : '');

/** 1. The sources, in code-unit order of path; a non-.md file is static. */
function readSources(b) {
  const files = [...b.input.files].sort((x, y) => byCodeUnits(x.path, y.path));
  for (const f of files) {
    if (f.path.endsWith('.md')) {
      b.sources.push({ path: f.path, text: f.content.includes('\r') ? f.content.replace(/\r\n?/g, '\n') : f.content });
    } else {
      b.statics.push({ path: f.path, content: f.content });
    }
  }
}

/** 2. Each source's front matter; refused sources and drafts are dropped. */
function frontMatter(b) {
  const kept = [];
  for (const s of b.sources) {
    const fm = parseFrontMatter(s.text);
    if ('error' in fm) {
      b.report.push(`refused ${s.path}: ${fm.error}`);
      continue;
    }
    s.data = fm.data;
    s.body = fm.body;
    s.post = s.path.startsWith('posts/');
    const own = RESERVED.find((d) => d !== 'posts' && s.path.startsWith(`${d}/`));
    if (own !== undefined) {
      b.report.push(`refused ${s.path}: ${own}/ is the generator's own`);
      continue;
    }
    if (s.post && !Object.hasOwn(s.data, 'date')) {
      b.report.push(`refused ${s.path}: a post needs a date`);
      continue;
    }
    const layout = s.data.layout ?? (s.post ? 'post' : 'page');
    if (!b.templates.has(layout)) {
      b.report.push(`refused ${s.path}: layout "${layout}" is no template that parses`);
      continue;
    }
    s.layout = layout;
    if (s.data.draft === true) {
      b.report.push(`draft ${s.path}`);
      continue;
    }
    kept.push(s);
  }
  b.sources = kept;
}

/** 3. Each page's directory and url; its slug made unique in its directory. */
function permalinks(b) {
  const taken = new Map();
  const takenIn = (dir) => {
    if (!taken.has(dir)) taken.set(dir, new Set(dir === '' ? RESERVED : []));
    return taken.get(dir);
  };
  for (const s of b.sources) {
    const dir = s.post ? 'posts' : dirOf(s.path);
    const slug = uniqueSlug(s.data.slug ?? slugify(s.data.title), takenIn(dir));
    s.slug = slug;
    s.outDir = dir === '' ? slug : `${dir}/${slug}`;
    s.url = `${b.base}/${s.outDir}/`;
    b.bySource.set(s.path, s);
  }
}

/** 4. Each body's Markdown, its links resolved to pages and static files. */
function markdown(b) {
  const staticPaths = new Set(b.statics.map((f) => f.path));
  for (const s of b.sources) {
    const dir = dirOf(s.path);
    const env = {
      link: (target) => {
        if (/^[A-Za-z][A-Za-z0-9+.-]*:/.test(target) || target.startsWith('/') || target.startsWith('#')) return target;
        const hash = target.indexOf('#');
        const rel = hash === -1 ? target : target.slice(0, hash);
        const frag = hash === -1 ? '' : target.slice(hash);
        const path = rel === '' ? null : resolvePath(dir, rel);
        if (path !== null && b.bySource.has(path)) return `${b.bySource.get(path).url}${frag}`;
        if (path !== null && staticPaths.has(path)) return `${b.base}/${path}${frag}`;
        b.broken.add(`broken-link ${s.path} -> ${target}`);
        return target;
      },
    };
    const md = renderMarkdown(s.body, env);
    s.html = md.html;
    s.toc = md.toc;
    s.excerpt = md.excerpt;
  }
}

/** 5. The posts, newest first and then by slug; each post's neighbours. */
function collections(b) {
  const posts = b.sources.filter((s) => s.post);
  posts.sort((x, y) => byCodeUnits(y.data.date, x.data.date) || byCodeUnits(x.slug, y.slug));
  b.posts = posts;
  posts.forEach((p, k) => {
    p.newer = k === 0 ? null : posts[k - 1];
    p.older = k === posts.length - 1 ? null : posts[k + 1];
  });
}

/** 6. The tags, grouped by slug and ordered by post count, then slug. */
function tags(b) {
  const bySlug = new Map();
  /** A source's tags, each slug once, in its own order. */
  const ownTags = (s) => {
    const seen = new Set();
    const out = [];
    for (const name of s.data.tags ?? []) {
      const slug = slugify(name);
      if (!seen.has(slug)) {
        seen.add(slug);
        out.push(name);
      }
    }
    return out;
  };
  for (const p of b.posts) {
    p.tagRefs = [];
    for (const name of ownTags(p)) {
      const slug = slugify(name);
      if (!bySlug.has(slug)) bySlug.set(slug, { name, slug, url: `${b.base}/tags/${slug}/`, posts: [] });
      const tag = bySlug.get(slug);
      tag.posts.push(p);
      p.tagRefs.push(tag);
    }
  }
  // A page's tags link to the posts' tag of the same slug, or to "" where no post has it.
  for (const s of b.sources) {
    if (!s.post) {
      s.tagRefs = ownTags(s).map((name) => {
        const slug = slugify(name);
        return bySlug.get(slug) ?? { name, slug, url: '', posts: [] };
      });
    }
  }
  b.tags = [...bySlug.values()].sort((x, y) => y.posts.length - x.posts.length || byCodeUnits(x.slug, y.slug));
}

/** A page's link record as templates read it. */
const linkOf = (s) => (s === null ? null : { title: s.data.title, url: s.url, date: s.data.date ?? '', date_long: s.data.date === undefined ? '' : longDate(s.data.date) });

/** A tag as templates read it (its posts as cards). */
const tagOf = (b, t) => ({ name: t.name, slug: t.slug, url: t.url, count: t.posts.length, posts: t.posts.map((p) => b.cards.get(p)) });

/** A post's card, as lists show it. */
function cardOf(s) {
  return {
    title: s.data.title,
    url: s.url,
    date: s.data.date ?? '',
    date_long: s.data.date === undefined ? '' : longDate(s.data.date),
    summary: s.data.summary ?? '',
    excerpt: s.excerpt,
    reading_minutes: Math.max(1, Math.ceil(wordsOf(s.body) / 200)),
    tags: s.tagRefs.map((t) => ({ name: t.name, slug: t.slug, url: t.url })),
  };
}

/** A page as its layout reads it. */
function pageOf(s) {
  return {
    ...cardOf(s),
    slug: s.slug,
    content: s.html,
    toc: s.toc.map((h) => ({ level: h.level, id: h.id, html: h.html })),
    newer: linkOf(s.newer ?? null),
    older: linkOf(s.older ?? null),
    is_post: s.post,
  };
}

/** 7. Every page through its layout, the index pages and the tag pages. */
function layouts(b) {
  b.cards = new Map(b.posts.map((p) => [p, cardOf(p)]));
  const site = { title: b.input.site.title, base_url: b.base };
  const allTags = b.tags.map((t) => ({ name: t.name, slug: t.slug, url: t.url, count: t.posts.length }));
  const recent = b.posts.slice(0, b.input.site.recent).map((p) => b.cards.get(p));
  const ctx = { templates: b.templates, escape: escapeHtml, analysis: b.analysis, memo: new Map(), memoConst: new Map() };
  const render = (name, vars) => {
    const nodes = b.templates.get(name);
    return nodes === undefined ? null : renderNodes(nodes, { vars: { site, tags: allTags, recent, ...vars }, parent: null }, ctx, 0);
  };
  for (const s of b.sources) b.output[`${s.outDir}/index.html`] = render(s.layout, { page: pageOf(s) });
  const per = b.input.site.per_page;
  const pages = Math.max(1, Math.ceil(b.posts.length / per));
  const indexUrl = (k) => (k === 1 ? `${b.base}/` : `${b.base}/page/${k}/`);
  for (let k = 1; k <= pages; k++) {
    const html = render('index', {
      posts: b.posts.slice((k - 1) * per, k * per).map((p) => b.cards.get(p)),
      pager: { number: k, total: pages, url: indexUrl(k), newer_url: k === 1 ? '' : indexUrl(k - 1), older_url: k === pages ? '' : indexUrl(k + 1) },
    });
    if (html !== null) b.output[k === 1 ? 'index.html' : `page/${k}/index.html`] = html;
  }
  for (const t of b.tags) {
    const html = render('tag', { tag: tagOf(b, t) });
    if (html !== null) b.output[`tags/${t.slug}/index.html`] = html;
  }
  const tagsHtml = render('tags', {});
  if (tagsHtml !== null) b.output['tags/index.html'] = tagsHtml;
  for (const f of b.statics) {
    if (Object.hasOwn(b.output, f.path)) b.report.push(`shadowed ${f.path}: a built page has its path`);
    else b.output[f.path] = f.content;
  }
}

/** 8. The report: every line reported above and each broken link, sorted, then the counts. */
function report(b) {
  const lines = [...b.report, ...b.broken].sort(byCodeUnits);
  const pages = b.sources.filter((s) => !s.post).length;
  lines.push(`built ${pages} pages, ${b.posts.length} posts, ${b.tags.length} tags and ${b.statics.length} static files`);
  b.output[REPORT_FILE] = `${lines.join('\n')}\n`;
}

const PIPELINE = Object.freeze([readSources, frontMatter, permalinks, markdown, collections, tags, layouts, report]);

/** One site's output tree: path -> text. */
export function run(input) {
  slugCache = new Map();
  const templates = new Map();
  const report = [];
  for (const name of Object.keys(input.templates).sort(byCodeUnits)) {
    try {
      templates.set(name, parseTemplate(name, input.templates[name]));
    } catch (err) {
      if (!(err instanceof TemplateError)) throw err;
      report.push(err.message);
    }
  }
  // Per-template free-variable + include-depth analysis (for memoisation).
  const analysis = new Map();
  const analysisMemo = new Map();
  for (const [name, nodes] of templates) {
    analyzeTemplate(name, nodes, templates, analysisMemo, new Set());
    analysis.set(name, analysisMemo.get(name) ?? null);
  }
  const b = {
    input,
    base: input.site.base_url.replace(/\/+$/, ''),
    templates,
    analysis,
    sources: [],
    statics: [],
    bySource: new Map(),
    broken: new Set(),
    report,
    posts: [],
    tags: [],
    cards: new Map(),
    output: {},
  };
  for (const plugin of PIPELINE) plugin(b);
  return b.output;
}
