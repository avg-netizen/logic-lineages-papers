module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryRefinementDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryRefinementRecognitionTargets
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalAtomicRefinementObjectTargets (sourceFields)
open NumberedWindowInternalAtomicApplicationShapeObjectTargets (auxAddressTerm freeTerm)
open NumberedWindowInternalNeutralAuxiliaryRefinement (freeAux auxDom auxFnType)

/-- Recognition at the original packed free-headed auxiliary address.
The two retained type reports refer to different physical fields. -/
def ExactOpenNeutralAuxiliaryRecognition : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
      (y c dom cod stored name arg : OTerm α),
    Nonempty (Derivation B Γ (equal y (auxAddressTerm c dom cod (freeTerm stored name) arg))) →
    Nonempty (Derivation B Γ
      (programGraph freeAux (numeral 1) ![y] ⊓
        (sourceFields y c cod ⊓
          (programGraph auxDom dom ![y] ⊓ programGraph auxFnType stored ![y]))))

end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryRefinementRecognitionTargets
