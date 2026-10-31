COTREE RESTRICTION REPAIR — work in progress, 30 October 2026

cotree-restriction.tex gives a self-contained hand proof of the faithful
induced-subgraph correspondence. It includes the two source counterexamples
and a separate obstruction to the tempting all-binary-parses JEP shortcut.

cotrees.py is the finite reference model. verify_restriction.py checks literal
selected vertices and all their edges, reducedness, and the three fixtures.
It is capped at six leaves, one worker, 512MiB/60s and the shared test mutex.
Run from this directory:
  python3 verify_restriction.py --report RESTRICTION-CONTROLS.json

RESTRICTION-CONTROLS.json records PASS on 1,619 ordered binary parses and
93,898 literal restrictions through six leaves, including all three fixtures.

verify_ac_states.py independently compares direct evaluation of all ordered
binary parses against state-set evaluation on their canonical cotrees. It
does not assume the original binary automaton's transitions associative or
commutative. AC-STATE-CONTROLS.json records PASS on every one of the 256 pairs
of two-state transition tables through five leaves and three three-state
examples through six leaves: 75,257 parse evaluations and 10,817 exact
canonical state-set comparisons. Equal child occurrences retain multiplicity.
Run this separate, equally bounded control with:
  python3 verify_ac_states.py --report AC-STATE-CONTROLS.json

The standalone mathematical note builds offline with Computer Modern:
  tectonic --only-cached --untrusted --keep-logs cotree-restriction.tex

This repairs the semantic representation step. It does not yet provide the
general JEP decision algorithm. L3 is working on that separate obligation in
../decision/. The canonical manuscript and accepted Lean target register must
not claim this partial repair is the entire decision theorem. No frozen Lean
source, external verification evidence or original manuscript is rewritten by
these files. The full existing paper03 width, bridge, certificate and age
results retain their separate status.
