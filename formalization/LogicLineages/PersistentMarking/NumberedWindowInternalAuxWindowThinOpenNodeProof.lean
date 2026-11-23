module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowThinTableProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowThinOpenNodeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalitySelf)
open ID1Completion.InternalLessThan (ltTest)
open ID1Completion.InternalLessThanSupportProof (acceptOfLess)
open ID1Completion.InternalControlGraphSupportProof (projectionValue successorValue)
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
open NumberedWindowInternalStrictAuxWindowThinTableProof (sameContext earlierValue exact_OpenContextMemoSuccessor)

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

private theorem childBits (T : Program 1) (dom cod : OTerm α) (xs : Fin 4 → OTerm α)
    (domField : Nonempty (Derivation body Γ (programGraph (childAt 0) dom xs)))
    (codField : Nonempty (Derivation body Γ (programGraph (childAt 1) cod xs)))
    (domOK : Nonempty (Derivation body Γ (unary T (suc z) dom)))
    (codOK : Nonempty (Derivation body Γ (unary T (suc z) cod)))
    (fnRow : Nonempty (Derivation body Γ (programGraph (measureAt 2) (suc (rawCons dom cod)) xs)))
    (argRow : Nonempty (Derivation body Γ (programGraph (measureAt 3) (suc dom) xs))) :
    Nonempty (Derivation body Γ (programGraph (admittedChildren T) (suc z) xs)) := by
  have codes := exactCodes dom cod xs domField codField
  let ft := suc (rawCons dom cod)
  let atype := suc dom
  have fnGood : Nonempty (Derivation body Γ (programGraph (reportTest 2 functionCode) (suc z) xs)) :=
    binaryGraph equalityTest (measureAt 2) functionCode (suc z) ft ft xs (equalitySelf ft) fnRow codes.1
  have argGood : Nonempty (Derivation body Γ (programGraph (reportTest 3 argumentCode) (suc z) xs)) :=
    binaryGraph equalityTest (measureAt 3) argumentCode (suc z) atype atype xs (equalitySelf atype) argRow codes.2.1
  unfold admittedChildren
  exact conjunctionAccept _ _ xs (unaryGraph T _ (suc z) dom xs domOK domField)
    (conjunctionAccept _ _ xs (unaryGraph T _ (suc z) cod xs codOK codField)
      (conjunctionAccept _ _ xs fnGood argGood))

theorem nodeValue (base : Program 2) (T : Program 1) (ctx dom cod fn arg old : OTerm α)
    (table : Nonempty (Derivation body Γ (contextTable (windowUpdate base T) old (priorKey dom cod fn arg) ctx)))
    (domOK : Nonempty (Derivation body Γ (unary T (suc z) dom)))
    (codOK : Nonempty (Derivation body Γ (unary T (suc z) cod)))
    (fnValue : Nonempty (Derivation body Γ (intrinsicGraph (selectedIntrinsic (windowUpdate base T))
      (suc (rawCons dom cod)) ctx fn)))
    (argValue : Nonempty (Derivation body Γ (intrinsicGraph (selectedIntrinsic (windowUpdate base T))
      (suc dom) ctx arg))) :
    Nonempty (Derivation body Γ (intrinsicGraph (selectedIntrinsic (windowUpdate base T))
      (suc cod) ctx (auxiliaryTerm dom cod fn arg))) := by
  let R := windowUpdate base T
  let prior := priorKey dom cod fn arg
  let parent := auxiliaryTerm dom cod fn arg
  let xs : Fin 4 → OTerm α := ![prior,old,ctx,z]
  let ft := suc (rawCons dom cod)
  let atype := suc dom
  have reports := fields (body := body) (Γ := Γ) dom cod fn arg old ctx
  have small := bothChildBounds (body := body) (Γ := Γ) dom cod fn arg
  have fnRow := earlierValue R 2 fn ft prior old ctx reports.function small.1
    ((sameContext R ft ctx fn).mp fnValue) table
  have argRow := earlierValue R 3 arg atype prior old ctx reports.argument small.2
    ((sameContext R atype ctx arg).mp argValue) table
  have fnEarlier := binaryGraph ltTest (childAt 2) currentKey (suc z) fn parent xs
    (acceptOfLess fn parent small.1) reports.function reports.key
  have argEarlier := binaryGraph ltTest (childAt 3) currentKey (suc z) arg parent xs
    (acceptOfLess arg parent small.2) reports.argument reports.key
  have before : Nonempty (Derivation body Γ (programGraph certain (suc z) xs)) :=
    conjunctionAccept shapeCheck _ xs reports.shape (conjunctionAccept (earlierAt 2) (earlierAt 3) xs fnEarlier argEarlier)
  have own := childBits T dom cod xs reports.domain reports.codomain domOK codOK fnRow argRow
  have enough := conjunctionAccept certain (admittedChildren T) xs before own
  have positive := (exactCodes dom cod xs reports.domain reports.codomain).2.2
  have updated : Nonempty (Derivation body Γ (contextStep R (suc cod) prior old ctx)) :=
    successorBranchIntro (conjunction certain (admittedChildren T)) (binaryAfter base (.projection 2) currentKey)
      resultCode (suc cod) z xs enough positive
  have next := exact_OpenContextMemoSuccessor R body α Γ (suc cod) prior old ctx table updated
  exact (sameContext R (suc cod) ctx parent).mpr next

#print axioms nodeValue

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowThinOpenNodeProof
