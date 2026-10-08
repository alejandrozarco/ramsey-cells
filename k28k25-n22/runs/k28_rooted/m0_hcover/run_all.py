#!/opt/homebrew/bin/python3.12
"""M0 driver: every (root, composition) family found in runs/k28_rooted/gen_*_r*_c*.json (denominator from OUTSIDE
this directory: 781 case files -> 53 families), smallest first; enum (3.12) -> hcover (3.9) -> validate (3.12).
Skips families whose result_*.json exists. usage: run_all.py [--skip TAG,...] [--controls N]"""
import glob, json, os, re, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__)); RUNS = os.path.abspath(os.path.join(HERE, '..'))
skip = set(sys.argv[sys.argv.index('--skip') + 1].split(',')) if '--skip' in sys.argv else set()
ctl = sys.argv[sys.argv.index('--controls') + 1] if '--controls' in sys.argv else '0'
fam = {}
for f in glob.glob(os.path.join(RUNS, 'gen_*_r*_c*.json')):
    if not re.fullmatch(r'gen_\d+_\d+_\d+_r\d+_c\d+\.json', os.path.basename(f)): continue
    r = json.load(open(f)); fam[(r['root'], tuple(r['composition']))] = r['before']
assert len(fam) == 53, len(fam)
for (k, c), n in sorted(fam.items(), key=lambda kv: kv[1]):
    tag = f"k{k}_c{c[0]}{c[1]}{c[2]}"
    if tag in skip or os.path.exists(os.path.join(HERE, 'data', tag, f'result_{tag}.json')): continue
    args = [str(k)] + [str(x) for x in c]
    if not os.path.exists(os.path.join(HERE, 'data', f'classes_{tag}.json')):
        subprocess.run(['nice', '-n', '10', '/opt/homebrew/bin/python3.12', os.path.join(HERE, 'enum_classes.py')] + args, check=True)
    subprocess.run(['nice', '-n', '10', '/usr/bin/python3', os.path.join(HERE, 'hcover.py')] + args + ['--controls', ctl], check=True)
    subprocess.run(['nice', '-n', '10', '/opt/homebrew/bin/python3.12', os.path.join(HERE, 'validate.py'), tag], check=True)
print('RUN_ALL DONE', flush=True)
