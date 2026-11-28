# The diagonal step of the calibration — source map (root lane, 27 November 2026)

Serves TARGETS.md "Ordinal inputs and assembly" item 2 (`AllTowerCalibration`) and the round-6 note
`local-fable-pair-2026-11-23-round6/opusA/CALIBRATION-INDUCTION-NOTE.md` ("What T5 needs beyond T4").

Targets: `LogicLineages.NativeModule.PersistentMarking.CollapseDiagonalTargets`
(`DiagonalHypotheses`, `DiagonalCollapse`). Proof: `…CollapseDiagonalProof.exact_DiagonalCollapse`.

## Statement

For any collapse data `D` satisfying (P), an index `top`, a family `p : countable ordinals → indices`, a
function `L` on the countable ordinals and a base value `Γ`, under `DiagonalHypotheses`:
`D.psi top` equals the least fixed point of `L` above `Γ`.

The hypotheses, in the paper's terms for n = 3 (`top = Ω^Ω`, `p e = Ω^e`, `L e = B_0^e(N_B)(0)`, `Γ = Γ_0`):

- (P); critical values are countable, at least `Γ`, closed under suprema of strictly increasing sequences;
  `1 < Γ`. All four are checked facts of the actual collapse (round 6).
- `L` strictly increasing, `e ≤ L e`, and at limits bounded by its earlier values.
- `L` has no fixed point in `[1, Γ]`.
- `Ω^e < Ω^Ω`; `|Ω^e| ≤ e`; every `η < Ω^Ω` with `|η| < e` is below `Ω^e`.
- T4 (`PsiPowerLevel`): `ψ(Ω^e) = L e` when `L` has no fixed point in `[1, e]`.

## Proof shape (as compiled)

Upper bound: the fixed point `fp` is critical (it is the supremum of `L^n(Γ)`, each a collapse value by
T4) and satisfies the clause at `top`: for `η < top` with `|η| < fp`, take `e = L(max(|η|, Γ)) < fp`; then
`η < p e` and (P) at `p e` gives `ψ(η) < L e < fp`. Lower bound: if `ψ(top) < fp`, closure of (P) at
`top` over the `p e` gives `L e < ψ(top)` for all `e < ψ(top)`, so `ψ(top)` or its predecessor is a fixed
point of `L` below `fp`.

## What is not claimed

No instance is asserted here. For n = 3 the hypotheses about `L` and about the powers of Ω still have to
be proved for the actual objects, and T4 is open (Fable A's lane). The lemma is level-independent on
purpose: at level `l` the same statement applies with `p e` the next tower of exponents and `L` the
level-`l+1` diagonal, which is where the general calibration induction would use it.
