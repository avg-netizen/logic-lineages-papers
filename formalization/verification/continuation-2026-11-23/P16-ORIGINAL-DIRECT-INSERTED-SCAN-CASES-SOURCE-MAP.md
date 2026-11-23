# P16: selected original raw inserted scan, open witness cases

Exact gate: `LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanCasesChecks`.
The two aliases are `exact_OpenOriginalInsertedScanCases` and `exact_OpenOriginalInsertedScanMemberCases`.

The first alias takes the physical selected scan graph at one, uses the actual
inserted sparse parser's object totality cases, rejects output zero with the
same poolReady guard, and recovers the exact scratch loop at one for the
successor's predecessor. The second applies the actual internal scan
membership induction, using an object proof of membership in the selected
scratch output, before opening the literal row callback's four witnesses.
The original removed input is kept through all relabelled contexts; the single
removed parser witness in Reports is the scratch input of the dominator report,
not an unrelated code. No index, multiplicity, installed d, or J is inferred.

Source dependencies: exact ordered scan (1795441629420270154-8), exact
unconditional row cases (1795441916877063698-8), exact scan membership
induction (1795442259534068523-8). Native gate for this package pending.

```
2c690f5fc2922eef7cc04959f43e880e14dc32f29f2af8c538dfda2518360deb  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalDirectInsertedScanCasesChecks.lean
c58c48794d2d2a1886b3182d752969a9f8eaf11f1305d96f893d8f20b700670d  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalDirectInsertedScanCasesProof.lean
d54134995cb0e24c79553497c3efeb9efe725c32ff2f6787d96810c9c609c925  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalDirectInsertedScanCasesTargets.lean
```
