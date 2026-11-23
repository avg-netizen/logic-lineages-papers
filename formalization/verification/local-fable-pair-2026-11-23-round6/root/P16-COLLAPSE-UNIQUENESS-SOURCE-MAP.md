# Paper 16: the characterization (P) determines the collapse

The printed proof of `lem:tower-cofinality` says it "uses the defining clause of this particular
collapse". Frozen `LogicLineages/PersistentMarking/ConditionalCollapseUniquenessTargets.lean`
(sha256 `15b2f00ec9e09e9566901a677bb5348cf6c53f4f8e960739bfc8207f426ee7d7`),
`CharacterizationDeterminesCollapse`: on a well-founded linear index order, two collapses with the same
coefficient norm and the same critical class that both satisfy `CharacterizationP` (#1463) are equal.
Proof: well-founded induction on the index; at each index both values are the least element of the same
set. Receipt `1795412992967601192-3312515` (first attempt `1795412976880710916-3312415` failed on an
argument name; draft kept under `drafts/root/`).

Use: once an actual collapse is defined by the clause (Opus A, this round), any other presentation of
ψ_B satisfying (P) — in particular the one cited from Simmons — is the same function, so the cited
calibration and endpoint identification can be stated against either. Existence of a function
satisfying (P) is not claimed here.

## Basic consequences of (P) (same round)

Frozen `LogicLineages/PersistentMarking/ConditionalCollapseBaseTargets.lean`
(sha256 `4008906546d5b48c7e9bfcc1635a265ac776e69d55282d16f9ec7f9883ecd5d9`), receipt
`1795414570897000128-3318265`, all under `CharacterizationP` alone:
- `CollapseAtMinimalIndex` — at an index with nothing below it the collapse is the least critical value
  (the abstract form of the calibration's n = 0 instance, #1488).
- `CollapseAboveMinimalValue` — that least critical value is a lower bound for every collapse value.
- `CollapseIncreasingOnSmallNorm` — on indices whose norm is below the least critical value the collapse
  is strictly increasing.
