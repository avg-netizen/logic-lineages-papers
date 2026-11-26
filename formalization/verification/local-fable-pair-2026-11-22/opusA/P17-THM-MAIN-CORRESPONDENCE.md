# Paper 17 `thm:main` vs. the Lean comparator `MainComparison` (Opus A, 2026-11-22)

Comparator: `LogicLineages/PermittedControl/GroundComparisonMainTargets.lean`
(frozen, sha256 `c3552aad…c4f`):

`MainComparison := Targets.FullControl ∧ Targets.NearControlModular ∧ GroundComparison.GroundComparison ∧ SelectedFunctionalHardnessTargets.SelectedFunctionalHardness`

| Printed phrase (paper.tex l.83–100) | Lean carrier | Verdict |
|---|---|---|
| "an explicit … control f_*" / "an explicit control f_b" | `factorialControl`, `nearControl b`, which are literal (see the `thm:arithmetic` table) | **covered** |
| "permitted" | No Lean predicate exists. The paper defines the framework in foundations.tex l.81–88: "any computable strictly increasing `f ≥ G`"; the constructed controls "are also primitive recursive, satisfy … eq:growth, and have an eventual upper bound", which are "sufficient conditions within the freedom of control described in [ww, §2.1]". `Targets.FullControl` (#010) = `ControlLaws` for both controls: even, `Primrec`, `G ≤ f`, `2^(2^{f n}) ≤ f(n+1)` (so strictly increasing), `f n < G(n+1)`, an eventual bound at a fixed hierarchy level, and the modular decrement. | **covered, with the restriction stated.** "Permitted" is carried by the paper's own sufficient conditions, every one present. No separate formalisation of WW §2.1 exists or is claimed. "Strictly increasing" is implied by the growth clause; it is not stated as its own conjunct. |
| "primitive recursive" | `ControlLaws.2.1 : Primrec f` | **covered** |
| "uniformly in a supplied computable admissible literal parsing policy" | (i): `∀ p : Policy, PolicyShape.Effective p → …` in `GroundDecidable`; (ii)/(iii): `∀ policy : Policy` in `SelectedFunctionalHardness`, with no effectivity needed | **covered, with the restriction stated.** For every such policy the claims hold, but the decider/reduction may depend on the policy; a procedure taking the policy as an input is not claimed. The hardness side is stronger: it holds for all policies. |
| (i) "Universal canonical weak comparison, strict comparison and equality are decidable for original T terms all of whose free variables have ground type. Bound variables, result types, internal types, and recursors are unrestricted." | `GroundComparison.GroundComparison` (thm:ground comparator) | **covered**, with the conventions of `P17-THM-GROUND-CORRESPONDENCE.md` (zero padding, one decider per policy/control/relation, correct on encoded typed terms) |
| (ii) "weak and strict comparison are undecidable for ground-output terms with free-variable levels at most one and internal type levels at most two, by a finite-query reduction" | #339: `FiniteQueryReduction ctrl policy true/false` and `¬HasComparisonDecider ctrl policy 2 true/false`. Terms are `OriginalTerm Γ .ground`, with `∀ τ ∈ Γ, τ.level ≤ 1` and `InternalLevelBound 2` | **covered** (accepted record #339; I did not re-read its proofs) |
| (iii) "single-query reduction when internal type levels at most three" | #339: `SingleQueryReduction ctrl policy true/false` and `¬HasComparisonDecider ctrl policy 3 …` | **covered** |
| "f_b equal to G on [0,b] and 0 ≤ f_b(n) − G(n) < 2 lcm(1,…,n) thereafter" | `Targets.NearControlModular`: `n ≤ b → f_b n = G n`; `G n ≤ f_b n`; `b < n → f_b n − G n < 2·initialLcm n`, with `initialLcm` = lcm(1..n) | **covered** |
| "For every supplied b, the same assertions hold" | `∀ b` in `GroundComparison` and in `FullControl`; `SelectedFunctionalHardness` is stated for every `SelectedWithThreshold ctrl K`, which includes every `nearControl b` | **covered** |

## Conclusion

The comparator is the printed `thm:main`. Its two named readings are inherited from `thm:ground`, plus one more: "permitted" is carried by the paper's own stated sufficient conditions (all of `lem:control`), not by a separate formalisation of Wilken–Weiermann §2.1. Uniformity in the policy means "for every policy", not "one procedure taking the policy as input". Clauses (ii) and (iii) are the accepted #339.

Status: `GroundComparisonMain.mainComparison : MainComparison` gated unconditionally, receipt `1795388718263284980-3166116`, axioms standard.
