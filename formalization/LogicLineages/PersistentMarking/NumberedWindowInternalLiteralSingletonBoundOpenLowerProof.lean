module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenLowerProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue successorValue)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalEqualityTestProof (rejectBackwardOrder)
open ID1Completion.InternalLessThan (ltTest)
open ID1Completion.InternalLessThanSupportProof (rejectOfGreater)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelope (applyUnary field)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalSparseRawTickShapeEmitterProof (consOfGraph)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalFreshProbeDispatchProgram (literal predOne)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralSingletonAtomsNumericProof (retainSingleton)
open NumberedWindowInternalLiteralSingletonBoundMachineProof
open NumberedWindowInternalLiteralSingletonBoundOpenRowsProof
open NumberedWindowInternalLiteralSingletonBoundOpenEvaluationProof (readBoundComparison)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The actual lower-index emitter rebuilds the literal node with the
predecessor of its successor-shaped index. -/
theorem exact_OpenBoundLowered (a d t i : OTerm α) :
    D B Γ (programGraph boundLowered (suc (boundTerm t i)) ![a,d,boundTerm t (suc i)]) := by
  let q := boundTerm t (suc i)
  let xs : Fin 3 → OTerm α := ![a,d,q]
  have rows := exact_OpenBoundRead (B := B) (Γ := Γ) t (suc i)
  have pred : D B Γ (unary predOne i (suc i)) := predecessorSuccessor i
  have reduced : D B Γ (unary (applyUnary predOne (field 1)) i q) := by
    apply compositionValue predOne (fun _ : Fin 1 => field 1) i ![q] ![suc i] pred
    intro k
    obtain rfl := Fin.eq_zero k
    exact rows.2.2
  have ty : D B Γ (programGraph boundType t xs) := onTape (field 0) 2 t xs rows.2.1
  have idx : D B Γ (programGraph loweredIndex i xs) :=
    onTape (applyUnary predOne (field 1)) 2 i xs reduced
  have tailGraph := consOfGraph loweredIndex (constantZero 3) i z xs idx (constantZeroValue xs)
  have bodyGraph := consOfGraph boundType (consOf loweredIndex (constantZero 3))
    t (rawCons i z) xs ty tailGraph
  have code : D B Γ (programGraph boundLowerCode (boundTerm t i) xs) :=
    consOfGraph (literal 3 1) (consOf boundType (consOf loweredIndex (constantZero 3)))
      (numeral 1) (rawCons t (rawCons i z)) xs (literalGraph 1 xs) bodyGraph
  apply compositionValue .succ (fun _ : Fin 1 => boundLowerCode) (suc (boundTerm t i))
    xs ![boundTerm t i] (successorValue ![boundTerm t i])
  intro k
  obtain rfl := Fin.eq_zero k
  exact code

/-- An index presented as a successor above the substitution depth
selects the lowered node with the same type field. -/
theorem exact_OpenSingletonBoundAboveDepth (V : Program 1) (H : Program 2) (U : Program 3)
    (a d t i : OTerm α) (inserted : D B Γ (unary V (suc z) a))
    (typedNode : D B Γ (unary V (suc z) (boundTerm t (suc i))))
    (above : D B Γ (ltF d (suc i))) :
    D B Γ (programGraph (singletonBound V H U) (suc (boundTerm t i))
      ![a,d,boundTerm t (suc i)]) := by
  let xs : Fin 3 → OTerm α := ![a,d,boundTerm t (suc i)]
  have before : D B Γ (programGraph boundBeforeDepth z xs) :=
    readBoundComparison ltTest a d t (suc i) z (rejectOfGreater (suc i) d above)
  have atDepth : D B Γ (programGraph boundAtDepth z xs) :=
    readBoundComparison equalityTest a d t (suc i) z (rejectBackwardOrder (suc i) d above)
  have unequal := zeroBranchIntro boundAtDepth boundLowered (shiftedInsertion H)
    (suc (boundTerm t i)) xs atDepth (exact_OpenBoundLowered a d t i)
  exact exact_OpenBoundProgram V H U a d t (suc i) (suc (boundTerm t i)) inserted typedNode
    (zeroBranchIntro boundBeforeDepth (branch boundAtDepth boundLowered (shiftedInsertion H))
      retainSingleton (suc (boundTerm t i)) xs before unequal)

#print axioms exact_OpenBoundLowered
#print axioms exact_OpenSingletonBoundAboveDepth
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenLowerProof
