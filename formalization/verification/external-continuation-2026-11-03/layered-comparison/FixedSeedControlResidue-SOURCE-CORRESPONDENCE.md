# Literal fixed-seed control residues

Subject label: `FixedSeedControlResidue3`. Source: `08-multivariate-collapse-comparison/paper.tex`, exact control `eq:f` at lines 94–100, accepted residue supplier `lem:residues` at lines 120–153, and the fixed-seed hypothesis and verification in the proof of `thm:snyatkov` at lines 156–190, especially 166–167 and 186–187. Source SHA-256: `3c2bf4cb4d8b6145acf67ce14c3d818bd20c572b6547b07d57d8598b45940b25`. This bounded draft follows verified checkpoint 37, `7c6181e9`, after `BalancedExactVariables`; it edits no accepted supplier.

The source requires eventual periodicity modulo every positive integer of the literal fixed-seed hyperfunction `H(0)=1`, `H(n+1)=f(H(n))`. Its last local verification is `H(n) ≥ n+1`, followed by `n ≥ m > 0 → H(n) ≡ r_m (mod m)`. This component isolates precisely that numerical obligation and its uniform effectiveness. It does not prove or assume the published quantified arithmetic decision theorem, an interpretation of its expanded language, or any whole balanced comparison theorem. Quantified Snyatkov/BASE decision remains PENDING; no numbered whole theorem is promoted by this draft.

## Literal fixed seed and unchanged exact control

`FixedSeedControlResidue.H n` is the ordinary computable definition `(Phi^[n]) 1`. Here `Phi` is the existing exact control `fastControl 5 (n + 100)`, and `fastControl` remains the accepted variable-seed hierarchy `F₀(n)=2^n`, `Fⱼ₊₁(n)=Fⱼ^[n+1](n)`. The new function uses the fixed seed **1**, at every index. It is not `fastControl n n`, a diagonal `F_j`, iteration seeded at `n`, or a redefinition of the hierarchy. No hierarchy or source definition changes.

The first target, `LiteralRecursionAndGrowth`, requires the seed equation, the exact one-step recursion at every natural index, the bound `n+1 ≤ H n` at every natural index, and `StrictMono H`. These facts are about the specified ordinary function, not hypotheses of the other targets. The seed and recursion follow from finite iteration. The accepted declaration `LogicLineages.OrdinalComparison.self_lt_Phi` in `Control.lean` supplies `x < Phi x`; induction supplies the displayed bound, and adjacent strict increase supplies strict monotonicity. No evaluation of a concrete large value is needed.

## Uniform numerical effectiveness and the existing residue

The second target, `UniformPrimitiveRecursiveData`, requires `Primrec H`, `Primrec fastControlResidue`, and `fastControlResidue m < m` for every `m > 0`. It uses the unchanged explicit witness `fastControlResidue m := fastControl 1 m % m` from `ControlResidueDefinitions.lean`. This already accepted witness realizes the source's common residue; no new CRT choice, opaque residue function, class field or residue-oracle premise is introduced.

Actual primitive recursion of `H` is available by finite iteration of the accepted `Phi_primrec` from `ControlComputability.lean`: the iteration count is the identity on `Nat`, the initial-value function is constant `1`, and the step ignores the external index and applies `Phi` to its state. This is the exact `Primrec.nat_iterate` API already used in `EncodedSuffixKernelProof.lean` lines 72–74. The existing declarations `fastControlResiduePrimitiveRecursive` and `fastControlResidueRange` in `ControlResidueProof.lean` supply the unchanged witness's effectiveness and range without new assumptions.

The eventual threshold is explicitly **m**, and the period is explicitly **1**, in the third target. Identity and a fixed constant are uniform primitive-recursive numerical choices; together with `Primrec fastControlResidue`, they give the effective data `(threshold, period, residue) = (m, 1, fastControlResidue m)`. No existentially selected threshold, variable-seed computation, supplied periodicity procedure or separate decision predicate appears in the specification. The modulus-zero value is left as the existing total natural function defines it; no positive-modulus assertion is extended to zero.

## Exact eventual threshold and period one

The third target, `EventualResidueAndPeriodOne`, says that for every positive `m` and every `n ≥ m`, both

1. `Nat.ModEq m (H n) (fastControlResidue m)`;
2. `Nat.ModEq m (H (n + 1)) (H n)`.

Thus it states the actual constant residue and literal period **one**, at the source's threshold **m**, rather than only an unspecified eventual period. `Nat.ModEq` is congruence of the actual natural values, not a substitute semantics.

The threshold is paid by the source argument without an off-by-one weakening: `n ≥ m > 0` makes `n` a successor, say `k+1`; the first target gives `H k ≥ k+1 = n ≥ m`. Therefore the last control application in `H n = Phi (H k)` has input at least `m`. The accepted declaration `phiShiftedConstantResidues` in `ControlResidueProof.lean` requires only `m - 100 ≤ H k`, which follows from this stronger input bound, and yields the first congruence with the same `fastControlResidue m`. Applying this result also at `n+1` and composing the two congruences yields the period-one clause. No stronger arbitrary-seed or hierarchy-wide new claim is needed.

## Three exact targets and planned candidates

1. `LiteralRecursionAndGrowth` / `literal_recursion_and_growth`: literal seed and recursion, the all-index `n+1` lower bound, and strict monotonicity of fixed-seed `H`.
2. `UniformPrimitiveRecursiveData` / `uniform_primitive_recursive_data`: actual `Primrec H`, actual primitive recursion of the unchanged common-residue function, and its positive-modulus range.
3. `EventualResidueAndPeriodOne` / `eventual_residue_and_period_one`: actual common residue and period one for every `n ≥ m > 0`, with explicit threshold `m`.

Planned candidate files, all ABSENT during this draft:

- `LogicLineages/OrdinalComparison/FixedSeedControlResidueGrowthProof.lean`: literal recurrence, lower bound and strict monotonicity using the unchanged control growth supplier.
- `LogicLineages/OrdinalComparison/FixedSeedControlResidueProgramsProof.lean`: fixed-seed primitive recursion and the existing effective residue/range package.
- `LogicLineages/OrdinalComparison/FixedSeedControlResidueResiduesProof.lean`: constant residue and period-one verification at threshold `m`.
- `LogicLineages/OrdinalComparison/FixedSeedControlResidueProof.lean`: thin import/export aggregation of the three obligations.

Definitions import only the accepted `ControlResidueDefinitions`; targets add the standard primitive-recursion, modular-congruence and monotonicity interfaces without importing candidate proofs. Candidates should use narrow accepted suppliers `Control`, `ControlComputability` and `ControlResidueProof`. Do not import a broad BASE decision proof or add any assumption that supplies the conclusion. Accepted axiom closures may use only the usual `propext`, `Classical.choice` and `Quot.sound` foundations.

This is a draft for parent/root exact-scope review. No comparison gate or prospective freeze has been run. Candidates must remain absent until root approval, comparator acceptance and prospective freeze. This step performs no candidate authoring, compiler invocation, accepted/frozen-file edit or Git operation. The separately required quantified Snyatkov arithmetic decision supplier remains PENDING.
