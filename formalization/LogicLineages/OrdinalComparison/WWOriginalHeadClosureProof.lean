module
public import LogicLineages.OrdinalComparison.WWOriginalHeadClosureTargets
public import LogicLineages.OrdinalComparison.WWOriginalDomainProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem originalHeadClosureValue : Targets.OriginalHeadClosureValue := by
  intro Γ σ ρ ρ' hh ho t
  induction t with
  | var c =>
    rcases c with ⟨τ, x, j⟩
    cases x with
    | here => simp [ordinalHeadClosure, substitute, ordinalHeadClosureComponent,
        expressionValue, denote, valuation, hh, closedValue]
    | there x => simp [ordinalHeadClosure, substitute, ordinalHeadClosureComponent,
        expressionValue, denote, valuation, ho]
  | zero => rfl
  | one => rfl
  | omega => rfl
  | add f g ihf ihg =>
    change ordinalNaturalSum (expressionValue ρ (ordinalHeadClosure f))
      (expressionValue ρ (ordinalHeadClosure g)) =
      ordinalNaturalSum (expressionValue ρ' f) (expressionValue ρ' g)
    rw [ihf, ihg]
  | emul f g ihf ihg =>
    change ordinalNaturalProduct ((2 : Ordinal) ^ expressionValue ρ (ordinalHeadClosure f))
      (expressionValue ρ (ordinalHeadClosure g)) =
      ordinalNaturalProduct ((2 : Ordinal) ^ expressionValue ρ' f) (expressionValue ρ' g)
    rw [ihf, ihg]
  | collapse f g ihf ihg =>
    change (actualCollapse (ordinalNaturalSum
      (ordinalNaturalProduct Ordinal.omega0 (expressionValue ρ (ordinalHeadClosure f)))
      (expressionValue ρ (ordinalHeadClosure g))) : Ordinal) =
      (actualCollapse (ordinalNaturalSum
      (ordinalNaturalProduct Ordinal.omega0 (expressionValue ρ' f))
      (expressionValue ρ' g)) : Ordinal)
    rw [ihf, ihg]

theorem originalHeadClosureNormPremise : Targets.OriginalHeadClosureNormPremise := by
  intro Γ σ f g hn ρ
  obtain ⟨ρ', hh, ho⟩ := originalHeadOneExtension Γ σ ρ
  rw [originalHeadClosureValue Γ σ ρ ρ' hh ho f,
    originalHeadClosureValue Γ σ ρ ρ' hh ho g]
  exact hn ρ'

theorem originalHeadClosureGrade : Targets.OriginalHeadClosureGrade := by
  intro Γ σ i t h
  induction h with
  | one i => exact .one i
  | omega i hi => exact .omega i hi
  | var x j =>
    cases x with
    | here => exact .one j.val
    | there y => exact .var y j
  | add hf hg ihf ihg => exact .add ihf ihg
  | emul hi hf hg ihf ihg => exact .emul hi ihf ihg
  | collapse hf hg hn ihf ihg =>
    exact .collapse ihf ihg (originalHeadClosureNormPremise _ _ _ _ hn)
  | promote hi hh hfree ih => exact .promote hi ih

end LogicLineages.OrdinalComparison.Source.OriginalDomain
