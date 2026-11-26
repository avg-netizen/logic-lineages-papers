module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonAtomsOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundMachineProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenRowsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderEqualityProof (equalityReject)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNeApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelope (nodeGood exactBody field applyUnary)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (packedNode)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell packedReports)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail cellGood)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalSparseRawRunRootTapeProof (rejectLeft rejectRight)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralAtomicRawGuardProof (freeTest bottomTest)
open NumberedWindowInternalLiteralSingletonAtomsNumericProof
open NumberedWindowInternalLiteralSingletonAtomsOpenProof (exact_OpenSingletonSyntax)
open NumberedWindowInternalLiteralSingletonBoundMachineProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def boundTerm {α : Type} (t i : OTerm α) : OTerm α :=
  rawCons (numeral 1) (packedBody [t,i])

theorem exact_OpenLiteralOtherTag (tag actual arity : Nat) (payload : List (OTerm α))
    (different : actual ≠ tag) :
    D B Γ (unary (nodeGood (literal 1 tag) arity) z (rawCons (numeral actual) (packedBody payload))) := by
  let q := rawCons (numeral actual) (packedBody payload)
  let test : Program 1 := .composition equalityTest ![cellHead,literal 1 tag]
  obtain ⟨cell⟩ := canonicalCell (body := B) (Γ := Γ) (numeral actual) (packedBody payload)
  have literalHead : D B Γ (unary cellHead (numeral actual) q) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cell)⟩
  have unequal : D B Γ (eqn (numeral actual : OTerm α) (numeral tag)).not :=
    ⟨Derivation.implicationIntroduction
      (numeralNeApply actual tag different (Derivation.hypothesis List.mem_cons_self))⟩
  have zero : D B Γ (unary test z q) := by
    apply compositionValue equalityTest ![cellHead,literal 1 tag] z ![q] ![numeral actual,numeral tag]
      (equalityReject _ _ unequal)
    intro i
    exact Fin.cases literalHead (Fin.cases (literalGraph tag ![q]) (fun j => Fin.elim0 j)) i
  let L := applyUnary (exactBody arity) cellTail
  exact rejectRight cellGood (conjunction test L) ![q]
    ⟨Derivation.conjunctionLeft cell⟩ (rejectLeft test L ![q] zero)

theorem exact_OpenBoundRead (t i : OTerm α) :
    D B Γ (unary boundShape (suc z) (boundTerm t i)) ∧
    D B Γ (unary (field 0) t (boundTerm t i)) ∧ D B Γ (unary (field 1) i (boundTerm t i)) := by
  let q := boundTerm t i
  have tag : D B Γ (unary (literal 1 1) (numeral 1) q) := literalGraph 1 ![q]
  have report := packedNode (literal 1 1) (numeral 1) [t,i] tag
  exact ⟨report.1,report.2.1,report.2.2.1⟩

theorem exact_OpenBoundProgram (V : Program 1) (H : Program 2) (U : Program 3)
    (a d t i out : OTerm α)
    (inserted : D B Γ (unary V (suc z) a))
    (typedNode : D B Γ (unary V (suc z) (boundTerm t i)))
    (computed : D B Γ (programGraph (boundInstance H) out ![a,d,boundTerm t i])) :
    D B Γ (programGraph (singletonBound V H U) out ![a,d,boundTerm t i]) := by
  let q := boundTerm t i
  let xs : Fin 3 → OTerm α := ![a,d,q]
  let fallback := branch (singletonSyntax V) (constantZero 3) (singletonBoundDispatch H U)
  have valid := exact_OpenSingletonSyntax V a d q inserted typedNode
  have isBound : D B Γ (bit (onRaw boundShape 2) xs) :=
    onTape boundShape 2 (suc z) xs (exact_OpenBoundRead t i).1
  have selected : D B Γ (programGraph (singletonBoundDispatch H U) out xs) :=
    successorBranchIntro (onRaw boundShape 2) U (boundInstance H) out z xs isBound computed
  have middle : D B Γ (programGraph fallback out xs) :=
    successorBranchIntro (singletonSyntax V) (constantZero 3) (singletonBoundDispatch H U)
      out z xs valid selected
  have notBottom : D B Γ (programGraph (onRaw bottomTest 2) z xs) :=
    onTape bottomTest 2 z xs (exact_OpenLiteralOtherTag 3 1 1 [t,i] (by decide))
  have notFree : D B Γ (programGraph (onRaw freeTest 2) z xs) :=
    onTape freeTest 2 z xs (exact_OpenLiteralOtherTag 0 1 2 [t,i] (by decide))
  have dis : D B Γ (programGraph (singletonAtomicDispatch fallback) out xs) :=
    zeroBranchIntro (onRaw freeTest 2) (branch (onRaw bottomTest 2) fallback retainSingleton) retainSingleton
      out xs notFree (zeroBranchIntro (onRaw bottomTest 2) fallback retainSingleton out xs notBottom middle)
  exact successorBranchIntro (singletonSyntax V) (constantZero 3) (singletonAtomicDispatch fallback)
    out z xs valid dis

#print axioms exact_OpenLiteralOtherTag
#print axioms exact_OpenBoundRead
#print axioms exact_OpenBoundProgram
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenRowsProof
