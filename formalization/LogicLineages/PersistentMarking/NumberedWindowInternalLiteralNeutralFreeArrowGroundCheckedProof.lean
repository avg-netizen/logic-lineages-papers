module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralArrowGroundCProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryFreeMembershipProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralFreeArrowGroundCheckedProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalCalculus
open ID1Completion.InternalControlGraph (equal)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalProbeTargets (OTerm typeCode)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalAtomicApplicationShape (refinedApplication)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm)
open NumberedWindowInternalApplicationOutputGuardTargets (outputGuard)
open NumberedWindowInternalNeutralAuxiliaryLiteralBodyProof (literalNeutral)
open NumberedWindowInternalNeutralAuxiliaryFreeMembershipProof (exact_OpenLiteralNeutralFreeAuxI)
open NumberedWindowInternalLiteralNeutralArrowGroundCProof
  (FreeAuxiliaryI exact_OpenLiteralNeutralFreeArrowGroundC)
open NumberedWindowComputabilityFormulaTargets (formula)

theorem exact_LiteralNeutralFreeAuxiliarySupply (i : Program 1) (r : Program 3) (c : Nat) :
    FreeAuxiliaryI i r c :=
  exact_OpenLiteralNeutralFreeAuxI i r c

/-- Same original free headed shape, genuine carrier in the same
selected literal ID₁, and no remaining auxiliary I premise. -/
theorem exact_OpenLiteralNeutralFreeArrowGroundCChecked
    (i : Program 1) (r p : Program 3) (c : Nat) (σ : ProbeTy)
    (α : Type) (Γ : List (Formula α)) (f ctx ty name : OTerm α)
    (declared : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (equal ty (numeral (typeCode (.arrow σ .ground))))))
    (shape : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (equal f (packedFreeTerm ctx ty name)))) :
    Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (formula (outputGuard i (refinedApplication p)) (.arrow σ .ground) f)) :=
  exact_OpenLiteralNeutralFreeArrowGroundC (p := p) (exact_LiteralNeutralFreeAuxiliarySupply i r c)
    σ f ctx ty name declared shape

#print axioms exact_LiteralNeutralFreeAuxiliarySupply
#print axioms exact_OpenLiteralNeutralFreeArrowGroundCChecked

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralFreeArrowGroundCheckedProof
