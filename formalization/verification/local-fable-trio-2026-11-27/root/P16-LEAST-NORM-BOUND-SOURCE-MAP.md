# The least norm bound of the formal ID₁ calculus — source map (root lane, 27 November 2026)

Serves `verification/paper16-remaining-targets-2026-11-25/TARGETS.md`, "Ordinal inputs and assembly",
item 3: "`LeastNormBound` names an independent arithmetic candidate. A source theorem must identify that
candidate with the cited ordinal before it can fill this role." The candidate's *existence* was not
recorded; these modules supply it, and say what can and cannot be concluded from it.

Targets: `LogicLineages.NativeModule.PersistentMarking.Paper16LeastNormBoundTargets`.
Proofs: `…Paper16LeastNormBoundProof` (light closure), `…Paper16LeastNormBoundHeightProof`.

## Paper context

`thm:upper` (ordinals.tex 315–333) applies "the published norm theorem" to an ID₁ proof of `I(tr s)`:
every provable atom has inductive norm below BH. In Lean that input is
`ExternalOrdinalInterfaceID1Targets.NormTheorem BH`, for an ordinal parameter `BH`.

## What is proved (no hypothesis)

| Target | Says | From |
| --- | --- | --- |
| `StagesExhaustLeast` | for a monotone operator on ℕ, the stages along the countable ordinals exhaust the least pre-fixed predicate | choice of a stage per element, `Ordinal.iSup_lt_omega_one`, `stageEq` |
| `BodyOperatorMonotone` | the operator of a positive body is monotone | `positiveMonotonicity` |
| `DerivableAtomsHaveStages` | a derivable atom `I(n)` lies in a countable stage | checked soundness of the calculus in the standard least model (`actualInternalCalculusSoundness`, `actualStandardLeastModel`), `interpretation` |
| `NormTheoremAtOmegaOne` | `NormTheorem ω₁` | previous row |
| `LeastNormBoundExists` | some `β ≤ ω₁` is the least ordinal with `NormTheorem β` | well-ordering |
| `LeastNormBoundUnique`, `NormTheoremIffAbove` | `β` is unique; `NormTheorem γ ↔ β ≤ γ` | order reasoning |

## What is proved from the paper's two own inputs

| Target | Says |
| --- | --- |
| `UpperAtLeastNormBound` | `UniformAccessibility ⟹ UpperStatement β`: `thm:upper` with the least norm bound in place of BH needs no cited theorem. |
| `HeightsBetween` | `UniformAccessibility`, `AllTowerCalibration` ⟹ `ψ(Λ) ≤ native height ≤ descending height ≤ β` for every signature. |
| `EndpointBelowLeastNormBound` | hence `ψ_B(ε_{Ω+1}) ≤ β`. |

## What is not claimed

- `β` is **not** identified with the Bachmann–Howard ordinal, nor with `ψ_B(ε_{Ω+1})`. By
  `NormTheoremIffAbove`, the remaining input `NormAtActualEndpoint` is equivalent to the single inequality
  `β ≤ ψ_B(ε_{Ω+1})`: the upper-bound half of the cited ordinal analysis of ID₁. The lower half follows
  from accessibility and calibration (last row), so the printed equalities need exactly that one
  inequality from the literature.
- `β < ω₁` is not proved (it would need countability of the formula syntax); only `β ≤ ω₁`.
- `NormTheorem` here ranges over the repository's formal calculus `Derivation`; whether that calculus is
  the ID₁ of the cited source is a source-correspondence question outside these modules.
- Nothing here changes the register: `thm:upper` at BH still needs the cited theorem.
