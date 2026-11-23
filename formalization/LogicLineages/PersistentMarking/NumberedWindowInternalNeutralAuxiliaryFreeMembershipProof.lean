module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryFreeMembershipCoreProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryBottomTargetShapeProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryFreeMembershipProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalAtomicApplicationShapeObjectTargets (auxAddressTerm freeTerm)
open NumberedWindowInternalNeutralAuxiliaryLiteralBodyProof (literalNeutral)
open NumberedWindowInternalNeutralAuxiliaryFreeMembershipCoreProof (exact_OpenLiteralNeutralFreeAuxICore)
open NumberedWindowInternalNeutralAuxiliaryBottomTargetShapeProof (exact_OpenNeutralBottomAuxTargetShapeCases)

/-- Fully pay the free-headed auxiliary successor cone in the exact
same literal ID1 definition. The source's genuine scalar carrier is
still necessary, as in the original accessibility introduction rule. -/
theorem exact_OpenLiteralNeutralFreeAuxI
    (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (x ctx dom cod stored name arg : OTerm α)
    (shape : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (equal x (auxAddressTerm ctx dom cod (freeTerm stored name) arg))))
    (held : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (carrier (literalNeutral i r) false c x))) :
    Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ (membership false x)) :=
  exact_OpenLiteralNeutralFreeAuxICore
    (fun B _ Δ y cc dd ee ss goal flags next =>
      exact_OpenNeutralBottomAuxTargetShapeCases (B := B) (Γ := Δ)
        y cc dd ee ss goal flags next)
    i r c α Γ x ctx dom cod stored name arg shape held

#print axioms exact_OpenLiteralNeutralFreeAuxI
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryFreeMembershipProof
