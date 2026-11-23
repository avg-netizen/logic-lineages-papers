module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaGroundStepProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryLiteralBodyProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryWholeBottomProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectSelectorsProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicLeastChecks
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTableProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
public import LogicLineages.PersistentMarking.NumberedWindowConcreteCheckers
public import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaBottomExitProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalAtomicRefinement (bottomTarget)
open NumberedWindowInternalAtomicRefinementObjectTargets (sourceFields)
open NumberedWindowInternalAtomicRefinementObjectSelectorsProof (literalAddress)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalLiteralRefinedAuxEdgeProof (lambdaAppCode)
open NumberedWindowInternalNeutralAuxiliaryWholeBottomProof (exact_OpenNeutralWholeBottom)
open NumberedWindowInternalNeutralAuxiliaryLiteralBodyProof (literalNeutral exact_OpenLiteralNeutralBottomI)
open NumberedWindowAtomicApplicationTargets (auxRaw)
open NumberedWindowAtomicApplicationTableProof (auxView)
open NumberedWindowAtomicRawStep (bottomRoot bottomRaw)
open NumberedWindowAtomicRawStepFieldProof (nodePacked)
open NumberedWindowAtomicLeastChecks (exact_AtomicLeastSingleton)
open NumberedWindowConcreteCheckers (root)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings least)
open NumberedWindowRootDispatchAlgorithm (check parts fixed)
open NumberedWindowAnnotationAlgorithm (annotations)
open NumberedWindowMarkRootAlgorithm (guarded)

/-- Exact numeric original bottom root at the actual lambda application
and the actual selected output, with the same physical root witness.
An existing least result cannot move this bare bottom representative. -/
theorem exact_OriginalLambdaBottomSelected (entries : Entries) (s : Settings)
    (ctx : List Nat) (ty dom cod rawFn arg rawDst selected : Nat)
    (accepted : root entries s (auxRaw dom cod rawFn arg) bottomRoot rawDst = true)
    (selection : least s ctx ty rawDst = some selected) :
    rawDst = bottomRaw cod ∧ selected = bottomRaw cod := by
  have branch : NumberedWindowMarkRootAlgorithm.bottom (auxRaw dom cod rawFn arg) rawDst = true := by
    simpa [root,check,bottomRoot,nodePacked,parts,fixed] using accepted
  have tyField : (annotations (auxRaw dom cod rawFn arg)).1 = cod := by
    simp [annotations,NumberedWindowAnnotationAlgorithm.termNext,auxView,
      NumberedWindowAnnotationAlgorithm.termParts,List.getD_eq_getElem?_getD]
  unfold NumberedWindowMarkRootAlgorithm.bottom guarded at branch
  rw [tyField,← bottomRaw] at branch
  simp only [Bool.and_eq_true,beq_iff_eq,and_assoc] at branch
  have h : rawDst = bottomRaw cod := branch.2.2.2.symm
  exact ⟨h,(exact_AtomicLeastSingleton s ctx ty cod).2.2 selected (h ▸ selection)⟩

/-- Genuine open nonbeta endpoint for the same neutral literal body:
the held physical bottomTarget check, not a semantic implication or
an assumed accessibility fact, identifies the target. The real
target carrier is explicitly retained. -/
theorem exact_OpenLiteralLambdaBottomExit (i : Program 1) (r : Program 3) (n : Nat)
    {α : Type} {Γ : List (Formula α)} (ctx dom cod body arg w y : OTerm α)
    (hit : Nonempty (Derivation (sourceBody (literalNeutral i r) n) Γ
      (programGraph bottomTarget (suc z) ![lambdaAppCode ctx dom cod body arg,w,y])))
    (carried : Nonempty (Derivation (sourceBody (literalNeutral i r) n) Γ
      (carrier (literalNeutral i r) false n y))) :
    Nonempty (Derivation (sourceBody (literalNeutral i r) n) Γ (membership false y)) := by
  let B := sourceBody (literalNeutral i r) n
  let raw := auxiliaryTerm dom cod (lambdaTerm dom body) arg
  obtain ⟨_,⟨cx⟩,⟨result⟩,_⟩ := literalAddress (body := B) (Γ := Γ) ctx cod raw
  have fields : Nonempty (Derivation B Γ (sourceFields (lambdaAppCode ctx dom cod body arg) ctx cod)) :=
    ⟨Derivation.conjunctionIntroduction cx result⟩
  have packed := exact_OpenNeutralWholeBottom
    (lambdaAppCode ctx dom cod body arg) w y ctx cod fields hit
  exact exact_OpenLiteralNeutralBottomI i r n α Γ y ctx cod packed carried

#print axioms exact_OriginalLambdaBottomSelected
#print axioms exact_OpenLiteralLambdaBottomExit
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaBottomExitProof
