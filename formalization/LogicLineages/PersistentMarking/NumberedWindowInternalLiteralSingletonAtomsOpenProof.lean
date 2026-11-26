module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonAtomsNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootDispatchOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionGuardFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonAtomsOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (packedNode)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralAtomicRawGuardProof (freeTest bottomTest)
open NumberedWindowInternalLiteralAtomicRawShapeProof (freeTerm bottomTerm freeReports)
open NumberedWindowInternalLiteralSingletonAtomsNumericProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenSingletonSyntax (V : Program 1) (a d q : OTerm α)
    (ha : D B Γ (unary V (suc z) a)) (hq : D B Γ (unary V (suc z) q)) :
    D B Γ (bit (singletonSyntax V) ![a,d,q]) :=
  conjunctionAccept _ _ ![a,d,q] (onTape V 0 (suc z) _ ha) (onTape V 2 (suc z) _ hq)

theorem exact_OpenSingletonRetain (a d q : OTerm α) :
    D B Γ (programGraph retainSingleton (suc q) ![a,d,q]) := by
  apply compositionValue .succ (fun _ : Fin 1 => .projection 2) (suc q) ![a,d,q] ![q] (successorValue ![q])
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 2 ![a,d,q]

theorem exact_OpenSingletonRetainFree (V : Program 1) (U : Program 3) (a d t n : OTerm α)
    (ha : D B Γ (unary V (suc z) a)) (hq : D B Γ (unary V (suc z) (freeTerm t n))) :
    D B Γ (programGraph (singletonAtoms V U) (suc (freeTerm t n)) ![a,d,freeTerm t n]) := by
  let q := freeTerm t n
  let xs : Fin 3 → OTerm α := ![a,d,q]
  have isFree : D B Γ (bit (onRaw freeTest 2) xs) := onTape freeTest 2 (suc z) xs (freeReports t n).1
  have dispatch : D B Γ (programGraph (singletonAtomicDispatch U) (suc q) xs) :=
    successorBranchIntro (onRaw freeTest 2) (branch (onRaw bottomTest 2) U retainSingleton) retainSingleton
      (suc q) z xs isFree (exact_OpenSingletonRetain a d q)
  exact successorBranchIntro (singletonSyntax V) (constantZero 3) (singletonAtomicDispatch U)
    (suc q) z xs (exact_OpenSingletonSyntax V a d q ha hq) dispatch

private theorem dispatchBottom (U : Program 3) (a d q : OTerm α)
    (isBottom : D B Γ (bit (onRaw bottomTest 2) ![a,d,q])) :
    D B Γ (programGraph (singletonAtomicDispatch U) (suc q) ![a,d,q]) := by
  let xs : Fin 3 → OTerm α := ![a,d,q]
  apply optionGraphCases (onRaw freeTest 2) xs _
  · intro β j Δ keep noFree
    simp only [programRename,sucRelabel,tripleInputsRename]
    rw [tripleInputsRename] at noFree
    let ys : Fin 3 → OTerm β := ![a.relabel j,d.relabel j,q.relabel j]
    have bottom := NumberedWindowInternalLiteralFunctionGuardFieldsProof.moveBit
      (onRaw bottomTest 2) a d q j Δ keep isBottom
    have hit := successorBranchIntro (onRaw bottomTest 2) U retainSingleton (suc (q.relabel j)) z ys bottom
      (exact_OpenSingletonRetain (a.relabel j) (d.relabel j) (q.relabel j))
    exact zeroBranchIntro (onRaw freeTest 2) (branch (onRaw bottomTest 2) U retainSingleton)
      retainSingleton (suc (q.relabel j)) ys noFree hit
  · intro β j Δ k _ yes
    simp only [programRename,sucRelabel,tripleInputsRename]
    rw [tripleInputsRename] at yes
    exact successorBranchIntro (onRaw freeTest 2) (branch (onRaw bottomTest 2) U retainSingleton)
      retainSingleton (suc (q.relabel j)) k ![a.relabel j,d.relabel j,q.relabel j] yes
      (exact_OpenSingletonRetain (a.relabel j) (d.relabel j) (q.relabel j))

/-- Actual compiled graph equation, not a numerical coincidence:
a singleton substitution retains a literal bottom at any depth. -/
theorem exact_OpenSingletonRetainBottom (V : Program 1) (U : Program 3) (a d t : OTerm α)
    (ha : D B Γ (unary V (suc z) a)) (hq : D B Γ (unary V (suc z) (bottomTerm t))) :
    D B Γ (programGraph (singletonAtoms V U) (suc (bottomTerm t)) ![a,d,bottomTerm t]) := by
  let q := bottomTerm t
  let xs : Fin 3 → OTerm α := ![a,d,q]
  have literalTag : D B Γ (unary (literal 1 3) (numeral 3) q) := literalGraph 3 ![q]
  have shape : D B Γ (unary bottomTest (suc z) q) :=
    (packedNode (literal 1 3) (numeral 3) [t] literalTag).1
  have isBottom : D B Γ (bit (onRaw bottomTest 2) xs) := onTape bottomTest 2 (suc z) xs shape
  exact successorBranchIntro (singletonSyntax V) (constantZero 3) (singletonAtomicDispatch U)
    (suc q) z xs (exact_OpenSingletonSyntax V a d q ha hq) (dispatchBottom U a d q isBottom)

#print axioms exact_OpenSingletonSyntax
#print axioms exact_OpenSingletonRetain
#print axioms exact_OpenSingletonRetainFree
#print axioms exact_OpenSingletonRetainBottom
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonAtomsOpenProof
