# Arbitrary original primitive mark decrease: proof candidate only

ARBITRARY-MARK-TARGET-1037 target-only passed28/28, peak495804 KiB,
receipt `1795084593264046362-6`, unchanged original caps and all30 pins.
Exited/reaped. The three new proof leaves remain unbuilt for
independent authored review.

- FiniteProof keeps original entire typed numbered head, base, extras,
  output and context. Induction on the actual natural leading label
  yields the real adjacency chain with exact count k−l, letting equal
  labels close only the non-strict finite helper at count zero.
- PrimitiveProof follows actual MarkDecrease. The omega mark uses one
  actual raw edge; all strict finite labels use the whole adjacency
  chain; each original lambda in the shared prefix lifts its same
  actual raw edge, with equal raw length and no primary-equivalence
  edge. No permitted marking of bottom, variable or auxApp.
- The established start-only full typed-window preservation closes the
  guards at all actual vertices of both traces, not a premise on
  intermediate or supplied terminal vertex. Checks prints both frozen
  support aliases. No assertion of Acc, I/J, ID1 coding or numbered result.

Static local closure 49 excludes prior stopped and complete numbered proofs.

```text
afb92e2e4c1664b406fc7e7deb375f58a7104ab21dd2752e7f733573e55f1f47  LogicLineages/PersistentMarking/NumberedWindowMarkPathFiniteProof.lean
4eddb6308821d6c1aa87851aec7227df989c5d24d25fa285582ed5e81244d855  LogicLineages/PersistentMarking/NumberedWindowMarkPathPrimitiveProof.lean
c7d30226fe10edf2abdda0376e5a77fec183e0e539309c634060c764f8a2830a  LogicLineages/PersistentMarking/NumberedWindowMarkPathChecks.lean
```
