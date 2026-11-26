# Actual period route: resource stop resolved, 21 November 2026

`ACTUAL-PERIOD-PARKED.md` stays as the historical record. This note supersedes its conclusion.

Cause of the stops. Receipt 1795226101580389178 (local reproduction of the parked stop, 10.8 s wall, 2.2 s
CPU) shows 1,371,896 kB of file-backed resident memory against 202,708 kB anonymous: the cap was reached by
the loaded import objects, not by elaboration. Importing `Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed`
alone stops a module at the cap (receipt 1795226211181844137, 1.7 s).

Changes, none to a target, definition, legacy module, checker or cap:
- `PeriodOddRootProof.lean` (new): a primitive q-th root in any algebraically closed field in which q is
  nonzero, from separability and splitting of X^q − 1 and the cyclic roots-of-unity group; then every odd q
  in `AlgebraicClosure (ZMod 2)`. Peak 1,271,496 kB.
- `PeriodTuple{Existence,Upper,Small,Exact}Proof.lean`, `PeriodTupleFactsStatementChecks.lean`: suppliers
  moved from `public import` to private `import`; `rootExists` uses the new lemma. Peaks 1.30–1.32 GB.
- `PeriodStateTupleProof.lean` (new): one state coincidence gives a Frobenius-periodic tuple. Its statement
  needs only `CartierOrbitDefinitions`; the Laurent bridge is a private import. Peak 1,534,444 kB.
- `ActualPeriodProof.lean`, `ActualPeriodStatementChecks.lean`: the legacy `ResidueTupleProof` import is
  replaced by the tuple-facts route. Peak 1,308,700 kB.

Superseded and failed editions: `../../local-claude-continuation-2026-11-21/superseded-sources/` and
`failed-editions/`; logs beside them. Final gate receipt 1795226431779775147-2681813
(`ACTUAL-PERIOD-NATIVE-RECEIPT.json`); evidence `ACTUAL-PERIOD-EVIDENCE.json` (79 modules, 0 errors).
