module

public import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowChildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowOpenProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalAcceptance (conjunction constantZero)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover constantZeroValue)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalBoundedDescentNormalizerStepSupportProof (conjunctionReject)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalLessThan (ltTest)
open ID1Completion.InternalLessThanSupportProof (acceptOfLess)
open ID1Completion.InternalControlGraphSupportProof (projectionValue successorValue valueUnique)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons unary)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePairGraphProof (consGraph)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (termReports)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey unaryAfter binaryAfter)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph binaryGraph)
open NumberedWindowInternalAuxMeasureStepTargets (certain shapeCheck childAt earlierAt measureAt)
open NumberedWindowInternalAuxMeasureOpenDataProof (priorKey bothChildBounds)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowInternalAuxWindowStepTargets
open NumberedWindowInternalAuxWindowOpenTargets
open NumberedWindowInternalStrictAuxWindowChildProof (recoverChild)
open NumberedWindowInternalStrictAuxWindowTargets
open NumberedWindowInternalChosenAuxMeasureMemoTargets (memoPrior)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private structure Fields (body : Positive (Fin 1)) (Γ : List (Formula α)) (xs : Fin 4 → OTerm α)
    (parent dom cod fn arg : OTerm α) : Prop where
  key : Nonempty (Derivation body Γ (programGraph currentKey parent xs))
  shape : Nonempty (Derivation body Γ (programGraph shapeCheck (suc z) xs))
  domain : Nonempty (Derivation body Γ (programGraph (childAt 0) dom xs))
  codomain : Nonempty (Derivation body Γ (programGraph (childAt 1) cod xs))
  function : Nonempty (Derivation body Γ (programGraph (childAt 2) fn xs))
  argument : Nonempty (Derivation body Γ (programGraph (childAt 3) arg xs))

private theorem fields (dom cod fn arg old ctx : OTerm α) :
    Fields body Γ ![priorKey dom cod fn arg,old,ctx,z] (auxiliaryTerm dom cod fn arg) dom cod fn arg := by
  let prior := priorKey dom cod fn arg
  let parent := auxiliaryTerm dom cod fn arg
  let xs : Fin 4 → OTerm α := ![prior,old,ctx,z]
  have key : Nonempty (Derivation body Γ (programGraph currentKey parent xs)) :=
    unaryGraph .succ (.projection 0) parent prior xs (successorValue ![prior]) (projectionValue 0 xs)
  obtain ⟨shape,read⟩ := termReports (body := body) (Γ := Γ) dom cod fn arg
  exact ⟨key,unaryGraph termShape currentKey (suc z) parent xs shape key,
    unaryGraph (field 0) currentKey dom parent xs read.1 key,
    unaryGraph (field 1) currentKey cod parent xs read.2.1 key,
    unaryGraph (field 2) currentKey fn parent xs read.2.2.1 key,
    unaryGraph (field 3) currentKey arg parent xs read.2.2.2.1 key⟩

private theorem exactCodes (dom cod : OTerm α) (xs : Fin 4 → OTerm α)
    (d : Nonempty (Derivation body Γ (programGraph (childAt 0) dom xs)))
    (c : Nonempty (Derivation body Γ (programGraph (childAt 1) cod xs))) :
    Nonempty (Derivation body Γ (programGraph functionCode (suc (rawCons dom cod)) xs)) ∧
    Nonempty (Derivation body Γ (programGraph argumentCode (suc dom) xs)) ∧
    Nonempty (Derivation body Γ (programGraph resultCode (suc cod) xs)) := by
  let arrow := rawCons dom cod
  have arrowGraph := binaryGraph fieldCons (childAt 0) (childAt 1) arrow dom cod xs (consGraph dom cod) d c
  exact ⟨unaryGraph .succ _ (suc arrow) arrow xs (successorValue ![arrow]) arrowGraph,
    unaryGraph .succ _ (suc dom) dom xs (successorValue ![dom]) d,
    unaryGraph .succ _ (suc cod) cod xs (successorValue ![cod]) c⟩

private theorem nonzeroAccept (T : Program 1) (cod : OTerm α) (xs : Fin 4 → OTerm α)
    (positive : Nonempty (Derivation body Γ (programGraph (strictAuxPositive T) (suc cod) xs))) :
    Nonempty (Derivation body Γ (programGraph (admittedChildren T) (suc z) xs)) := by
  let G := conjunction certain (admittedChildren T)
  let P := programGraph G (suc z) xs
  apply formulaCases P _
  · have got := conjunctionRecover certain (admittedChildren T) xs
      (body := body) (Gamma := P :: Γ) ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨got⟩ := got
    exact ⟨Derivation.conjunctionRight got⟩
  · have reject := conjunctionReject certain (admittedChildren T) xs
      (body := body) (Gamma := P.not :: Γ) ⟨Derivation.hypothesis List.mem_cons_self⟩
    have mismatch := zeroBranchElim G (constantZero 4) resultCode (suc cod) xs reject
      (withHyp positive P.not)
    obtain ⟨bad⟩ := valueUnique (constantZero 4) (suc cod) z xs mismatch (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩

private theorem typeReport (T : Program 1) (slot : Nat) (ty : OTerm α) (xs : Fin 4 → OTerm α)
    (selected : Nonempty (Derivation body Γ (programGraph (childAt slot) ty xs)))
    (taken : Nonempty (Derivation body Γ (programGraph (unaryAfter T (childAt slot)) (suc z) xs))) :
    Nonempty (Derivation body Γ (unary T (suc z) ty)) := by
  apply compositionRecover T (fun _ : Fin 1 => childAt slot) (suc z) xs ![ty] taken
  intro j
  obtain rfl := Fin.eq_zero j
  exact selected

theorem exact_OpenStrictAuxWindowRow : ExactOpenStrictAuxWindowRow := by
  intro base T body α Γ ctx dom cod fn arg old R prior table actual
  let xs : Fin 4 → OTerm α := ![prior,old,ctx,z]
  have select := fields (body := body) (Γ := Γ) dom cod fn arg old ctx
  have small := bothChildBounds (body := body) (Γ := Γ) dom cod fn arg
  have positive := successorBranchElim shapeCheck (binaryAfter base (.projection 2) currentKey)
    (strictAuxPositive T) (suc cod) z xs select.shape actual
  have children := nonzeroAccept T cod xs positive
  let f := reportTest 2 functionCode
  let a := reportTest 3 argumentCode
  let t0 := unaryAfter T (childAt 0)
  let t1 := unaryAfter T (childAt 1)
  obtain ⟨a0⟩ := conjunctionRecover t0 (conjunction t1 (conjunction f a)) xs children
  obtain ⟨a1⟩ := conjunctionRecover t1 (conjunction f a) xs ⟨Derivation.conjunctionRight a0⟩
  obtain ⟨flags⟩ := conjunctionRecover f a xs ⟨Derivation.conjunctionRight a1⟩
  have codes := exactCodes dom cod xs select.domain select.codomain
  obtain ⟨dc⟩ := typeReport T 0 dom xs select.domain ⟨Derivation.conjunctionLeft a0⟩
  obtain ⟨cc⟩ := typeReport T 1 cod xs select.codomain ⟨Derivation.conjunctionLeft a1⟩
  obtain ⟨fnWin⟩ := recoverChild R functionCode 2 ctx prior old fn (rawCons dom cod)
    small.1 select.function codes.1 ⟨Derivation.conjunctionLeft flags⟩ table
  obtain ⟨argWin⟩ := recoverChild R argumentCode 3 ctx prior old arg dom
    small.2 select.argument codes.2.1 ⟨Derivation.conjunctionRight flags⟩ table
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction dc cc)
    (Derivation.conjunctionIntroduction fnWin argWin)⟩

#print axioms exact_OpenStrictAuxWindowRow

end LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowOpenProof
