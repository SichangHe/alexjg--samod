# usage: python3 -I diff_orig.py   (run from anywhere)
# For each function copied into verus/samod_verified.rs, print a unified diff of its body against the original
# samod-core source, after dropping blank lines, `proof { }` blocks and `// CHANGE` comments from the copy.
import re, difflib, os, sys
here = os.path.dirname(os.path.abspath(__file__))
orig = open(os.path.join(here, '../samod-core/src/actors/document/peer_doc_connection.rs')).read()
ver = open(os.path.join(here, 'samod_verified.rs')).read()
ver = ver[ver.index('impl PDC'):]
def body(src, name):
    m = re.search(r'fn ' + name + r'\b[^{]*\{', src, re.S)
    i = m.end(); depth = 1
    while depth:
        c = src[i]; depth += (c == '{') - (c == '}'); i += 1
    return src[m.end():i - 1]
def strip_proofs(b):
    out = []; i = 0
    while True:
        j = b.find('proof {', i)
        if j < 0: out.append(b[i:]); break
        out.append(b[i:j]); k = j + 7; depth = 1
        while depth:
            depth += (b[k] == '{') - (b[k] == '}'); k += 1
        i = k
    return ''.join(out)
def norm(b, v):
    if v: b = strip_proofs(b)
    lines = [re.sub(r'\s+', ' ', l).strip() for l in b.splitlines()]
    return [l for l in lines if l and not l.startswith('//')]
for fn in ['reset_sync_state', 'prepare_request', 'receive_sync_message', 'generate_sync_messages']:
    a = norm(body(orig, fn), False); b = norm(body(ver, fn), True)
    print('=== ' + fn + (' (identical modulo comments/proofs)' if a == b else ''))
    for l in difflib.unified_diff(a, b, 'original', 'verus', lineterm='', n=0): print(l)
