module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchGraphSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchGraphProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalObjectFiberSourceDispatch InternalOriginalObjectFiberSourceDispatchGraphSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalAcceptanceConjunctionProof InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalCanonicalFixedWindowVertexDispatchSupportProof SourceComputabilityFormulaSupportProof
open InternalBetaTotalityProof
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualInternalOriginalObjectSourcePositiveGraph :
    InternalOriginalObjectFiberSourceDispatchTargets.ActualInternalOriginalObjectSourcePositiveGraph := by
  intro window Gamma data oldPositive body α Delta context functionObject targetObject source target certificate out
  let a := positivePremises window Gamma context functionObject targetObject source target
  let xs := positiveArguments context functionObject targetObject certificate
  have ha : Nonempty (Derivation body (a :: Delta) a) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ht : Nonempty (Derivation body (a :: Delta)
      (programGraph (positiveActivation window Gamma) (suc z) xs)) :=
    conjunctionAccept _ _ xs (coordinateEqualityAccept 4 0 window xs (andLeft ha))
      (conjunctionAccept _ _ xs
        (leftTestAccept 1 (Encodable.encode Gamma) xs (andLeft (andLeft (andRight ha))))
        (leftTestAccept 2 (Encodable.encode Gamma) xs (andLeft (andRight (andRight ha)))))
  obtain ⟨h⟩ := compositionDispatch (positiveActivation window Gamma) oldPositive
    (InternalPathChecker.checker (InternalCanonicalQuotientEdgeSelection.edgeChecker data) true)
    ![rightOf (.projection 1),rightOf (.projection 2),.projection 3] out xs
    (Fin.cons source (Fin.cons target (Fin.cons certificate Fin.elim0))) ht
    (positiveInputs xs source target
      (andIntro (andRight (andLeft (andRight ha))) (andRight (andRight (andRight ha)))))
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualInternalOriginalObjectSourceTypedGraph :
    InternalOriginalObjectFiberSourceDispatchTargets.ActualInternalOriginalObjectSourceTypedGraph := by
  intro window Gamma data oldTyped body α Delta context typ object payload out
  let a := typedPremises window Gamma context object payload
  let xs := typedArguments context typ object
  have ha : Nonempty (Derivation body (a :: Delta) a) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ht : Nonempty (Derivation body (a :: Delta)
      (programGraph (typedActivation window Gamma) (suc z) xs)) :=
    conjunctionAccept _ _ xs (coordinateEqualityAccept 3 0 window xs (andLeft ha))
      (leftTestAccept 2 (Encodable.encode Gamma) xs (andLeft (andRight ha)))
  obtain ⟨h⟩ := compositionDispatch (typedActivation window Gamma) oldTyped
    (InternalCanonicalDescentSelection.selectedTyped data)
    ![rightOf (.projection 2),.projection 1] out xs
    (Fin.cons payload (Fin.cons typ Fin.elim0)) ht
    (typedInputs xs payload (andRight (andRight ha)))
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualInternalOriginalObjectSourceResultGraph :
    InternalOriginalObjectFiberSourceDispatchTargets.ActualInternalOriginalObjectSourceResultGraph := by
  intro window Gamma data oldResult body α Delta context domain codomain functionObject argumentObject function argument out
  rw [pairedApplicationEq]
  let a := resultPremises window Gamma data context domain codomain functionObject argumentObject function argument
  let xs := resultArguments context domain codomain functionObject argumentObject
  let ys : Fin 4 → OTerm α := Fin.cons domain (Fin.cons codomain (Fin.cons function (Fin.cons argument Fin.elim0)))
  let gs : Fin 4 → Program 5 := ![.projection 1,.projection 2,rightOf (.projection 3),rightOf (.projection 4)]
  let g := programGraph (result window Gamma data oldResult) out xs
  let b := paired (Encodable.encode Gamma) (InternalCanonicalQuotientEdgeApplicationLift.actualJ data) out ys
  have ha : Nonempty (Derivation body (a :: Delta) a) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨ht⟩ := resultTestAccept window Gamma data context domain codomain functionObject argumentObject function argument ha
  have hg := resultInputs xs function argument (andRight (andLeft ha)) (andRight (andLeft (andRight ha)))
  have hgf (i : Fin 4) := (hg i).map (fun d => addHyp d g)
  have hgb (i : Fin 4) := (hg i).map (fun d => addHyp d b)
  obtain ⟨hf⟩ := pairCompositionRecover (Encodable.encode Gamma)
    (InternalCanonicalQuotientEdgeApplicationLift.actualJ data) gs out xs ys hgf
    (successorBranchElim (resultActivation window Gamma data) oldResult (resultBranch Gamma data)
      out z xs ⟨addHyp ht g⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have hp : Nonempty (Derivation body (b :: a :: Delta)
      (paired (Encodable.encode Gamma) (InternalCanonicalQuotientEdgeApplicationLift.actualJ data) out ys)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := successorBranchIntro (resultActivation window Gamma data) oldResult (resultBranch Gamma data)
    out z xs ⟨addHyp ht b⟩ (pairCompositionAccept (Encodable.encode Gamma)
      (InternalCanonicalQuotientEdgeApplicationLift.actualJ data) gs out xs ys hgb hp)
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

theorem actualInternalOriginalObjectSourcePositiveZeroGraph :
    InternalOriginalObjectFiberSourceDispatchTargets.ActualInternalOriginalObjectSourcePositiveZeroGraph := by
  intro window Gamma data oldPositive body α Delta xs out
  obtain ⟨h⟩ := actualOriginalZeroBranch body 4 (positiveActivation window Gamma) oldPositive (positiveBranch data) α out xs
  exact ⟨weakenClosed h Delta⟩

theorem actualInternalOriginalObjectSourceTypedZeroGraph :
    InternalOriginalObjectFiberSourceDispatchTargets.ActualInternalOriginalObjectSourceTypedZeroGraph := by
  intro window Gamma data oldTyped body α Delta xs out
  obtain ⟨h⟩ := actualOriginalZeroBranch body 3 (typedActivation window Gamma) oldTyped (typedBranch data) α out xs
  exact ⟨weakenClosed h Delta⟩

theorem actualInternalOriginalObjectSourceResultZeroGraph :
    InternalOriginalObjectFiberSourceDispatchTargets.ActualInternalOriginalObjectSourceResultZeroGraph := by
  intro window Gamma data oldResult body α Delta xs out
  obtain ⟨h⟩ := actualOriginalZeroBranch body 5 (resultActivation window Gamma data) oldResult (resultBranch Gamma data) α out xs
  exact ⟨weakenClosed h Delta⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchGraphProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchGraphProof
