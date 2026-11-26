# Paper 16 `thm:upper` (ordinals.tex 315–333) against `ConditionalUpperTargets` (Opus B, round 4)

Comparator `UpperStatement BH := ConfinedStrictWellFounded ∧ UpperBound BH` (frozen sha256
e43ba411d5e9b8d5ca367d26d6898c6807e69107cb37d92e616eb45bff8022e9). Hypotheses: E4 `NormTheorem BH` (Opus A, verbatim),
R1 `IndividualAccessibility` (own form).

| printed step | carrier |
|---|---|
| "The confined strict relation is well founded" | #489 `exact_ConfinedStrictWellFounded` (external route, not the printed derivation from arithmetic accessibility) |
| "Every descendant of s remains in S = Ty(s)"; "positive-edge simulation gives rk_⊐(s) ≤ rk_{R_S}(tr s)" | #1460 `exact_ConfinedRankBelowTaggedStageNorm` (rank of q ≤ least stage of `taggedStep (support q)` at the tagged canonical address of tr q's class) |
| "The arithmetic accessibility proof supplies an ID₁ proof of the individual I-membership of tr(s) in this fixed window" | hypothesis R1 `IndividualAccessibility` at that address (admitted by `exact_ActualClassAddressSpecification`) |
| "The tagged I component has its standalone accessibility norm" | proved: `bodyOperatorOfEvaluating` (from `exact_InterpretsEvaluatingPrograms` + `exact_ActualOperatorAndTerms`) — the body operator of the presentation **is** `taggedStep S K`; `ConditionalUpperBridgeProof.exact_BodyStageBridge` records the stage identity |
| "Applying the published norm theorem yields rk_{R_S}(tr s) < BH" | hypothesis E4 `NormTheorem BH`; the least-stage property of #1460 turns the stage below BH into the bound |

R1 form. Faithful: the individual form (the printed proof uses exactly "the individual I-membership of tr(s)"; the
lemma's proof ends "an ID₁ proof of the stated individual memberships"). Opus A's `InternalAccessibility d c` is the
uniform all-terms sentence — stronger. It would imply the individual form by internal ∀-elimination at the address
numeral, internal Σ₁-truth of the scalar checker graph formula at that numeral, and the closed-term identity
`tagTerm false (numeral x) = numeral (2x)`; none of these is in the repository as a lemma, so that bridge is not claimed.
Not needed: the fixed-type-versus-whole-universe rank equality (the symbolic side is the full confined relation; the
norm side is the address relation of #1455).
