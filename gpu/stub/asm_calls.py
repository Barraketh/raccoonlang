# Rewrites each one-line `asm volatile("…" : outs : ins : clobbers);` of generated CUDA into calls of the stub's
# `gpu_asm_out`/`gpu_asm_in`, so a host compiler checks the operand expressions (and sees outputs as written) while
# only ptxas can check the template itself. Reads the kernel on stdin and writes it to stdout.
import re, sys

def split_top(text, sep):
    """Splits `text` at `sep` outside strings and parentheses."""
    parts, depth, quoted, start, i = [], 0, False, 0, 0
    while i < len(text):
        ch = text[i]
        if quoted:
            if ch == "\\": i += 1
            elif ch == '"': quoted = False
        elif ch == '"': quoted = True
        elif ch == "(": depth += 1
        elif ch == ")": depth -= 1
        elif ch == sep and depth == 0:
            parts.append(text[start:i]); start = i + 1
        i += 1
    parts.append(text[start:])
    return parts

def operands(section):
    """The C++ expressions of a comma-separated `"c"(expr)` operand list."""
    out = []
    for op in split_top(section, ","):
        m = re.fullmatch(r'\s*"[^"]*"\((.*)\)\s*', op)
        if m: out.append(m.group(1))
    return out

asm = re.compile(r'^(\s*)asm volatile\((.*)\);$')
for line in sys.stdin:
    m = asm.match(line.rstrip("\n"))
    if not m:
        sys.stdout.write(line); continue
    sections = split_top(m.group(2), ":")
    outs = operands(sections[1]) if len(sections) > 1 else []
    ins = operands(sections[2]) if len(sections) > 2 else []
    print(f"{m.group(1)}gpu_asm_out({', '.join(outs)}); gpu_asm_in({', '.join(ins)});")
