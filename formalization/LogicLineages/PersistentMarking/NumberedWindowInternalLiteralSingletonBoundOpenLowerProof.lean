module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
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
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralSingletonAtomsNumericProof (retainSingleton)
open NumberedWindowInternalLiteralSingletonBoundMachineProof
open NumberedWindowInternalLiteralSingletonBoundOpenRowsProof
open NumberedWindowInternalLiteralSingletonBoundOpenEvaluationProof (readBoundComparison)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The actual `predOne` on a successor-shaped term, through the literal
AST identity with the original predecessor program. -/
theorem exact_OpenPredOneSuccessor (i : OTerm α) : D B Γ (unary predOne i (suc i)) := by
  rw [exact_DispatchControlAST.2.2.1]
  exact predecessorSuccessor i

/-- The actual lower-index emitter on an arbitrary open index `i`.
Given a graph of the actual `predOne` at `i` with output `j`, it rebuilds the
literal node with the same type field and index `j`. No order premise is
needed here; only the branch selection uses `d < i`. -/
theorem exact_OpenBoundLoweredOfPredecessor (a d t i j : OTerm α)
    (pred : D B Γ (unary predOne j i)) :
    D B Γ (programGraph boundLowered (suc (boundTerm t j)) ![a,d,boundTerm t i]) := by
  let q := boundTerm t i
  let xs : Fin 3 → OTerm α := ![a,d,q]
  have rows := exact_OpenBoundRead (B := B) (Γ := Γ) t i
  have reduced : D B Γ (unary (applyUnary predOne (field 1)) j q) := by
    apply compositionValue predOne (fun _ : Fin 1 => field 1) j ![q] ![i] pred
    intro k
    obtain rfl := Fin.eq_zero k
    exact rows.2.2
  have ty : D B Γ (programGraph boundType t xs) := onTape (field 0) 2 t xs rows.2.1
  have idx : D B Γ (programGraph loweredIndex j xs) :=
    onTape (applyUnary predOne (field 1)) 2 j xs reduced
  have tailGraph := consOfGraph loweredIndex (constantZero 3) j z xs idx (constantZeroValue xs)
  have bodyGraph := consOfGraph boundType (consOf loweredIndex (constantZero 3))
    t (rawCons j z) xs ty tailGraph
  have code : D B Γ (programGraph boundLowerCode (boundTerm t j) xs) :=
    consOfGraph (literal 3 1) (consOf boundType (consOf loweredIndex (constantZero 3)))
      (numeral 1) (rawCons t (rawCons j z)) xs (literalGraph 1 xs) bodyGraph
  apply compositionValue .succ (fun _ : Fin 1 => boundLowerCode) (suc (boundTerm t j))
    xs ![boundTerm t j] (successorValue ![boundTerm t j])
  intro k
  obtain rfl := Fin.eq_zero k
  exact code

/-- The successor-shaped row is the instance `i := suc i`, `j := i`. -/
theorem exact_OpenBoundLowered (a d t i : OTerm α) :
    D B Γ (programGraph boundLowered (suc (boundTerm t i)) ![a,d,boundTerm t (suc i)]) :=
  exact_OpenBoundLoweredOfPredecessor a d t (suc i) i (exact_OpenPredOneSuccessor i)

/-- An arbitrary open index above the substitution depth selects the
lowered node. The strict comparison and the equality test both reject on
the derivation of `d < i`; the index of the output is the designated value
`j` of the actual `predOne` at `i`. -/
theorem exact_OpenSingletonBoundAbovePredecessor (V : Program 1) (H : Program 2) (U : Program 3)
    (a d t i j : OTerm α) (inserted : D B Γ (unary V (suc z) a))
    (typedNode : D B Γ (unary V (suc z) (boundTerm t i)))
    (above : D B Γ (ltF d i)) (pred : D B Γ (unary predOne j i)) :
    D B Γ (programGraph (singletonBound V H U) (suc (boundTerm t j))
      ![a,d,boundTerm t i]) := by
  let xs : Fin 3 → OTerm α := ![a,d,boundTerm t i]
  have before : D B Γ (programGraph boundBeforeDepth z xs) :=
    readBoundComparison ltTest a d t i z (rejectOfGreater i d above)
  have atDepth : D B Γ (programGraph boundAtDepth z xs) :=
    readBoundComparison equalityTest a d t i z (rejectBackwardOrder i d above)
  have unequal := zeroBranchIntro boundAtDepth boundLowered (shiftedInsertion H)
    (suc (boundTerm t j)) xs atDepth (exact_OpenBoundLoweredOfPredecessor a d t i j pred)
  exact exact_OpenBoundProgram V H U a d t i (suc (boundTerm t j)) inserted typedNode
    (zeroBranchIntro boundBeforeDepth (branch boundAtDepth boundLowered (shiftedInsertion H))
      retainSingleton (suc (boundTerm t j)) xs before unequal)

/-- An index presented as a successor above the substitution depth
selects the lowered node with the same type field. -/
theorem exact_OpenSingletonBoundAboveDepth (V : Program 1) (H : Program 2) (U : Program 3)
    (a d t i : OTerm α) (inserted : D B Γ (unary V (suc z) a))
    (typedNode : D B Γ (unary V (suc z) (boundTerm t (suc i))))
    (above : D B Γ (ltF d (suc i))) :
    D B Γ (programGraph (singletonBound V H U) (suc (boundTerm t i))
      ![a,d,boundTerm t (suc i)]) :=
  exact_OpenSingletonBoundAbovePredecessor V H U a d t (suc i) i inserted typedNode above
    (exact_OpenPredOneSuccessor i)

#print axioms exact_OpenPredOneSuccessor
#print axioms exact_OpenBoundLoweredOfPredecessor
#print axioms exact_OpenBoundLowered
#print axioms exact_OpenSingletonBoundAbovePredecessor
#print axioms exact_OpenSingletonBoundAboveDepth
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenLowerProof
