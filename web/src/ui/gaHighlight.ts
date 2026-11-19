// Lightweight, XSS-safe Geometric Algebra Syntax Highlighter for CoffeeShop IDE
// Pure display tokenizer — zero character-width drift so textarea caret alignment stays 100% exact.

function escapeHtml(raw: string): string {
  return raw.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

const TOKEN_RE =
  /(\/\/[^\n]*|--[^\n]*|\/\*[\s\S]*?\*\/)|("(?:\\.|[^"\\])*"|'(?:\\.|[^'\\])*')|(@(?:basis|param)\b)|((?:0x|#)([0-9a-fA-F]{6})\b)|\b(e[0-5]+|et|ex|ey|ez|no|ni|ori|inf|pss|I)\b|\b(Algebra|let|fn|for|in|if|else|return|graph|slider|point|plane|line|motor|translator|transform|sphere|circle|rotor|boost|seg|poly|mesh|curve|slice|implicit|surface|opns|draggable|exp|log|norm|normalized|Normalized|grade|inv|conj|dual|rev|sin|cos|tan|sqrt|abs|preset)\b|(>>>|<<|[\^&~!*+\-/=])|\b(\d+(?:\.\d+)?)\b/g;

export function highlightGaCode(source: string): string {
  if (!source) return '\n';

  let out = '';
  let lastIndex = 0;
  TOKEN_RE.lastIndex = 0;

  let m: RegExpExecArray | null;
  while ((m = TOKEN_RE.exec(source)) !== null) {
    if (m.index > lastIndex) {
      out += escapeHtml(source.slice(lastIndex, m.index));
    }

    const full = m[0]!;
    if (m[1]) {
      out += `<span class="tok-comment">${escapeHtml(full)}</span>`;
    } else if (m[2]) {
      out += `<span class="tok-string">${escapeHtml(full)}</span>`;
    } else if (m[3]) {
      out += `<span class="tok-directive">${escapeHtml(full)}</span>`;
    } else if (m[4] && m[5]) {
      const hex = `#${m[5].toLowerCase()}`;
      out += `<span class="tok-hex" style="--swatch:${hex}">${escapeHtml(full)}</span>`;
    } else if (m[6]) {
      out += `<span class="tok-blade">${escapeHtml(full)}</span>`;
    } else if (m[7]) {
      out += `<span class="tok-kw">${escapeHtml(full)}</span>`;
    } else if (m[8]) {
      out += `<span class="tok-op">${escapeHtml(full)}</span>`;
    } else if (m[9]) {
      out += `<span class="tok-num">${escapeHtml(full)}</span>`;
    } else {
      out += escapeHtml(full);
    }

    lastIndex = TOKEN_RE.lastIndex;
  }

  if (lastIndex < source.length) {
    out += escapeHtml(source.slice(lastIndex));
  }

  // Trailing newline keeps <pre> scrollHeight identical to <textarea> when ending on an empty line
  return source.endsWith('\n') ? `${out}\n` : out;
}
