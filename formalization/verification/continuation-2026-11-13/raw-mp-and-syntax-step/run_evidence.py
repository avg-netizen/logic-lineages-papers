#!/usr/bin/env python3
"""Portable coordinator-only invocation. Default prints argv; --run performs evidence only."""
from pathlib import Path
import argparse, hashlib, importlib.util, json, sys
HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if (p/'scripts/check.py').is_file())
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()
def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--run',action='store_true');args=parser.parse_args()
 cfg=json.loads((HERE/'CONFIG.json').read_text());verifier=ROOT/cfg['verifier'];frozen=ROOT/cfg['frozen_file']
 for path,digest in [(verifier,cfg['verifier_sha256']),(ROOT/'scripts/check.py',cfg['checker_sha256']),(frozen,cfg['frozen_sha256'])]:
  if sha(path)!=digest:raise SystemExit('Configured immutable input changed: '+str(path))
 argv=[str(verifier),'--base',cfg['baseline_commit'],'--frozen-file',str(frozen)]
 for g in cfg['gate_roots']:argv+=['--gate',g]
 for a in cfg['required_exact_aliases']:argv+=['--alias',a]
 for a in cfg['allowed_mutable_paths']:
  if a!='formalization/AGENTS.md':argv+=['--allow-inherited',a]
 if not args.run:
  print(json.dumps({'status':'prepared-not-run','argv':argv,'output_packet':str(HERE.relative_to(ROOT))},indent=2));return 0
 spec=importlib.util.spec_from_file_location('adopted_bounded_verifier',verifier)
 v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
 # Only output destination is rebound. Original checker ROOT/BUILD, verifier
 # __file__/hash, source selection and every verification check stay unchanged.
 v.HERE=HERE;sys.argv=argv
 return v.main()
if __name__=='__main__':sys.exit(main())
