# Paper 17 `thm:ground` vs. the Lean comparator `GroundComparison` (Opus A, 2026-11-22)

Comparator: `LogicLineages/PermittedControl/GroundComparisonTargets.lean`
(frozen, sha256 `1c4d4020…6d2e91`), in namespace `PermittedControl.GroundComparison`:

`GroundComparison := GroundDecidable factorialControl ∧ ∀ b, GroundDecidable (nearControl b)`

`GroundDecidable ctrl := ∀ p : Policy, PolicyShape.Effective p → ∀ rel, ∃ decide : ℕ×ℕ×ℕ → Bool, Computable decide ∧ ∀ Γ ground, ∀ τ υ (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ), decide (Γ.length, encodeTerm a, encodeTerm b) = true ↔ Canonical ctrl p rel a b`

Printed statement (consequences.tex l.9): "For either f_* or a fixed f_b, universal weak comparison,
Wilken–Weiermann strict comparison, and universal equality of canonical assignments are decidable for
original Gödel T terms whose free variables all have ground type. There is no bound on internal types,
bound-variable types, result types, recursor instances, or finite nesting." The definitions are in paper.tex l.76–80.

| Printed phrase | Lean carrier | What it says | Verdict |
|---|---|---|---|
| "either f_* or a fixed f_b" | `factorialControl`, `nearControl b` (see the `thm:arithmetic` table) | Literal controls. The decider may depend on `b`. | **covered** |
| "Fix one computable admissible literal parsing policy ρ" (consequences.tex l.3) | `p : Policy` (`Source.AdmissibleSum.Policy`), `StandardControlCurrent.PolicyShape.Effective p` | Every policy of the accepted policy type with the accepted effectivity predicate, i.e. the same hypotheses as #261 `Programs`. | **covered**, as accepted for #257/#261. Admissibility is the `Policy` type itself; I did not re-derive that the type matches the printed admissibility clause. |
| "canonical assignments" (zero-history assignment of the literal term) | `AdmissibleAssignment.assignment p t : Option (OrdinalVector Γ τ.level)` | The literal policy assignment, the same function #257 and #261 are stated for. `Canonical` asks for both assignments to exist. They always do for ground Γ (#261 `TypedImage`). | **covered** |
| "original Gödel T terms whose free variables all have ground type" | `OriginalTerm Γ τ`, `∀ σ ∈ Γ, σ = Ty.ground` | Typed original terms. Only the context is restricted. | **covered** |
| "no bound on internal types, bound-variable types, result types, recursor instances, or finite nesting" | `τ υ : Ty` arbitrary, and different for the two terms; `OriginalTerm` unrestricted | Nothing bounds the term or its types. | **covered** |
| "universal … under all admissible valuations" (paper.tex l.76) | `∀ s : SelectedSourceDomain.AdmissibleSubstitution ctrl Γ` inside `Holds` | The quantifier ranges over the selected control's admissible substitution class (graded closed expressions with the norm bound). For ground Γ these are exactly the positive naturals, by `GroundComparisonDomain.selectedGroundDomain` (gated). | **covered** |
| "weak comparison means universal coordinatewise inequality" | `Holds .weak := ∀ s j, vectorAt a s j ≤ vectorAt b s j` | Coordinatewise `≤` of ordinal values. | **covered, with zero padding.** Vectors of different levels are compared with missing coordinates read as `0` (`vectorAt`). This is the reading the proof uses ("zero padding beyond the assigned level"). The definition in paper.tex does not say how different lengths compare; this is the only interpretive choice. |
| "Wilken–Weiermann strict comparison means universal strict inequality in coordinate zero and universal weak inequality in every positive coordinate" | `Holds .strict := (∀ s, vectorAt a s 0 < vectorAt b s 0) ∧ ∀ s j, 0 < j → ≤` | Literal. | **covered** (zero padding as above) |
| "Equality is universal coordinatewise equality" | `Holds .equal := ∀ s j, vectorAt a s j = vectorAt b s j` | Literal. | **covered** (zero padding as above) |
| "are decidable" | `∃ decide : ℕ × ℕ × ℕ → Bool, Computable decide ∧ …`, input `(Γ.length, encodeTerm a, encodeTerm b)` | One Mathlib-computable Boolean procedure per (control, policy, relation), correct on every pair of encoded typed terms. | **covered, with the restriction stated.** It is uniform in the terms but not claimed uniform in the policy or in `b`; there is a separate decider per policy and per `b`. Nothing is claimed on codes that are not `encodeTerm` of a typed term (Paper 18's `RawEquality` has that extra clause; this comparator does not). |

**Not claimed:** quantifier alternation, functional free variables (that is `thm:functional-hardness`, #339),
equality of assignments to `G`'s, and running time.

## Conclusion

The comparator is the printed theorem, read with two conventions that are only implicit in the paper. Different-length vectors are compared with zero padding, which is the convention the printed proof uses. There is one decider per policy, per control and per relation, correct on encoded typed terms only. Nothing is weakened relative to the printed statement: types and nesting are unrestricted, and the substitution class is the paper's own.

Status: `GroundComparison.groundComparison : GroundComparison` gated unconditionally, receipt `1795388718263284980-3166116`, axioms standard.
