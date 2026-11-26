1. `ls verification/local-fable-pair-2026-11-22` succeeded, listing `BRIEF.md`, `briefs`, `drafts`, `fable2`, `gate.sh`, `import_graph.py`, `logs`, `opusA`, `opusB`, `PRIOR-LOCAL-RUN-POLICY.json`, `__pycache__`, `RELEASE.md`, `root`, `warm.py`.
2. `bash verification/local-fable-pair-2026-11-22/gate.sh` exited with code 1 and printed `gate.sh: line 11: 1: profile`, which is the expected usage error.
3. The Write tool created `verification/local-fable-pair-2026-11-22/fable2/SMOKE.txt` containing `ok`.
