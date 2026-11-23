module

public import LogicLineages.PersistentMarking.NumberedWindowInternalApplicationOutputGuardTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalApplicationOutputGuardOpenProof
open FirstOrder Language
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm suc z)
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open NumberedWindowGuardedGraphTargets (atSlot)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalCoordinateTargets (RawDomain)
open NumberedWindowInternalApplicationOutputGuardTargets

/-- Same object context, unchanged body, and the same actual output term. -/
theorem exact_OpenApplicationOutputGuard (i : Program 1) (p : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (f u y : OTerm α)
    (h : Nonempty (Derivation body Γ (accepts (outputGuard i p) f u y))) :
    Nonempty (Derivation body Γ (accepts p f u y)) ∧
    Nonempty (Derivation body Γ (RawDomain i y)) := by
  let xs : Fin 3 → OTerm α := ![f,u,y]
  obtain ⟨both⟩ := conjunctionRecover p (atSlot i 2) xs h
  have checked : Nonempty (Derivation body Γ (RawDomain i (xs 2))) := by
    apply compositionRecover i (fun _ => .projection 2) (suc z) xs ![xs 2]
      ⟨Derivation.conjunctionRight both⟩
    intro a
    obtain rfl := Fin.eq_zero a
    exact projectionValue 2 xs
  exact ⟨⟨Derivation.conjunctionLeft both⟩, checked⟩

#print axioms exact_OpenApplicationOutputGuard
end LogicLineages.PersistentMarking.NumberedWindowInternalApplicationOutputGuardOpenProof
