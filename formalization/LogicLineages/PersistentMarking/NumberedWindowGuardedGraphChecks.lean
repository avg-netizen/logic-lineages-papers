module
public import LogicLineages.PersistentMarking.NumberedWindowGuardedGraphTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
public section
namespace LogicLineages.PersistentMarking.NumberedWindowGuardedGraphChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm suc z)
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open NumberedWindowGuardedGraphTargets
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalCoordinateTargets (RawDomain)

theorem exact_GuardEvaluation : GuardEvaluation := by
  intro i p f u v
  unfold NumberedWindowGuardedGraphTargets.guard
  rw [actualConjunctionEvaluation _ _ _ _,actualConjunctionEvaluation _ _ _ _]
  change (if evaluate i (f ::ᵥ nil) = 1 ∧
    (if evaluate i (u ::ᵥ nil) = 1 ∧ evaluate p (f ::ᵥ u ::ᵥ v ::ᵥ nil) = 1 then 1 else 0) = 1
    then 1 else 0) = _
  split_ifs <;> simp_all

private theorem extract {α : Type} {body : Positive (Fin 1)} {Γ : List (Formula α)}
    (i : Program 1) (p : Program 3) (f u v : OTerm α)
    (h : Nonempty (Derivation body Γ (accepts (guard i p) f u v))) :
    Nonempty (Derivation body Γ (RawDomain i f)) ∧ Nonempty (Derivation body Γ (RawDomain i u)) ∧
      Nonempty (Derivation body Γ (accepts p f u v)) := by
  let xs : Fin 3 → OTerm α := ![f,u,v]
  obtain ⟨outer⟩ := conjunctionRecover (atSlot i 0) (ID1Completion.InternalAcceptance.conjunction (atSlot i 1) p) xs h
  obtain ⟨inner⟩ := conjunctionRecover (atSlot i 1) p xs ⟨Derivation.conjunctionRight outer⟩
  have slot (k : Fin 3) (hk : Nonempty (Derivation body Γ (programGraph (atSlot i k) (suc z) xs))) :
      Nonempty (Derivation body Γ (RawDomain i (xs k))) := by
    apply compositionRecover i (fun _ => .projection k) (suc z) xs ![xs k] hk
    intro a
    obtain rfl := Fin.eq_zero a
    exact projectionValue k xs
  exact ⟨slot 0 ⟨Derivation.conjunctionLeft outer⟩,
    slot 1 ⟨Derivation.conjunctionLeft inner⟩, ⟨Derivation.conjunctionRight inner⟩⟩

theorem exact_GuardRules : GuardRules := by
  intro i j r d p
  constructor
  · intro c body α Γ f u v h
    obtain ⟨hf,hu,_⟩ := extract i p f u v h
    exact ⟨(NumberedWindowInternalCoordinateChecks.exact_DomainRules i j r d false c body α Γ f).mpr hf,
      (NumberedWindowInternalCoordinateChecks.exact_DomainRules i j r d false c body α Γ u).mpr hu⟩
  · intro unique body α Γ f u v w hv hw
    exact unique body α Γ f u v w (extract i p f u v hv).2.2 (extract i p f u w hw).2.2

#print axioms exact_GuardEvaluation
#print axioms exact_GuardRules
end LogicLineages.PersistentMarking.NumberedWindowGuardedGraphChecks
