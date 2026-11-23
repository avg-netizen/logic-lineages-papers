module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryRefinementRecognitionTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliarySameFieldProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryBottomTargetProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult)
open NumberedWindowInternalAtomicRefinement (atTarget)
open NumberedWindowInternalAtomicRefinementObjectTargets (sourceFields)
open NumberedWindowInternalAuxBottomRefinement (sourceFlag)
open NumberedWindowInternalNeutralAuxiliaryRefinement (auxDom auxFnType bottomAuxTarget sameField)
open NumberedWindowInternalNeutralAuxiliarySameFieldProof (exact_OpenSameFieldTarget)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Invert just the accepted bottom-auxiliary target guard on the actual
source/witness/target tape. Keep its right argument unspecified. -/
theorem exact_OriginalNeutralBottomAuxTarget
    (x w y c cod dom stored : OTerm α)
    (fields : Nonempty (Derivation B Γ
      (sourceFields x c cod ⊓ (unary auxDom dom x ⊓ unary auxFnType stored x))))
    (accepted : Nonempty (Derivation B Γ (programGraph bottomAuxTarget (suc z) ![x,w,y]))) :
    Nonempty (Derivation B Γ
      (unary sourceFlag (suc z) y ⊓
        (sourceFields y c cod ⊓ (unary auxDom dom y ⊓ unary auxFnType stored y)))) := by
  unfold bottomAuxTarget at accepted
  rw [exact_DispatchControlAST.2.2.2.2.2,exact_DispatchControlAST.2.2.2.2.2,
    exact_DispatchControlAST.2.2.2.2.2,exact_DispatchControlAST.2.2.2.2.2] at accepted
  let xs : Fin 3 → OTerm α := ![x,w,y]
  let domFn := conjunction (sameField auxDom) (sameField auxFnType)
  let resDomFn := conjunction (sameField rawResult) domFn
  let ctxResDomFn := conjunction (sameField rawContext) resDomFn
  obtain ⟨h0⟩ := conjunctionRecover (atTarget sourceFlag) ctxResDomFn xs accepted
  obtain ⟨h1⟩ := conjunctionRecover (sameField rawContext) resDomFn xs ⟨Derivation.conjunctionRight h0⟩
  obtain ⟨h2⟩ := conjunctionRecover (sameField rawResult) domFn xs ⟨Derivation.conjunctionRight h1⟩
  obtain ⟨h3⟩ := conjunctionRecover (sameField auxDom) (sameField auxFnType) xs ⟨Derivation.conjunctionRight h2⟩
  have slot : Nonempty (Derivation B Γ (programGraph (atTarget sourceFlag) (suc z) xs)) :=
    ⟨Derivation.conjunctionLeft h0⟩
  unfold atTarget at slot
  have flag : Nonempty (Derivation B Γ (unary sourceFlag (suc z) y)) := by
    apply compositionRecover sourceFlag (fun _ : Fin 1 => .projection (2 : Fin 3)) (suc z) xs ![y] slot
    intro k
    obtain rfl := Fin.eq_zero k
    exact projectionValue 2 ![x,w,y]
  obtain ⟨f⟩ := fields
  have pair := Derivation.conjunctionLeft f
  have types := Derivation.conjunctionRight f
  obtain ⟨ctx⟩ := exact_OpenSameFieldTarget rawContext x w y c
    ⟨Derivation.conjunctionLeft pair⟩ ⟨Derivation.conjunctionLeft h1⟩
  obtain ⟨res⟩ := exact_OpenSameFieldTarget rawResult x w y cod
    ⟨Derivation.conjunctionRight pair⟩ ⟨Derivation.conjunctionLeft h2⟩
  obtain ⟨dom'⟩ := exact_OpenSameFieldTarget auxDom x w y dom
    ⟨Derivation.conjunctionLeft types⟩ ⟨Derivation.conjunctionLeft h3⟩
  obtain ⟨fn'⟩ := exact_OpenSameFieldTarget auxFnType x w y stored
    ⟨Derivation.conjunctionRight types⟩ ⟨Derivation.conjunctionRight h3⟩
  obtain ⟨ok⟩ := flag
  exact ⟨Derivation.conjunctionIntroduction ok
    (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction ctx res)
      (Derivation.conjunctionIntroduction dom' fn'))⟩

#print axioms exact_OriginalNeutralBottomAuxTarget
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryBottomTargetProof
