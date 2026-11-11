module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceWeightApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityFuelProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceWeightLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalPairingSumBounds InternalRecursionClosureLogicProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open OriginalHereditaryValidityInternalRecurrenceWeightSelectorProof
open OriginalHereditaryValidityInternalRecurrenceWeightApplicationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem lambdaPayloadCases (state raw child payload : OTerm alpha) (psi : Formula alpha)
    (hr : Nonempty (Derivation body Delta (graph1 currentRaw raw state)))
    (hb : Nonempty (Derivation body Delta (graph1 currentBody child state)))
    (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload raw)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 1) raw)))
    (k : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (bp : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 InternalUnpair.right bp (child.relabel j))) →
      Nonempty (Derivation body Theta (weakBound (suc bp) (payload.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let qs : Fin 3 → Program 1 := ![rawMiddle,leftOf rawMiddle,OriginalLambdaConstructor.bodyPayload]
  let xs : Fin 1 → OTerm alpha := Fin.cons raw Fin.elim0
  apply queryCases qs xs psi
  intro beta j ys Theta hj hq
  simp only [xs,consTermRename,emptyRename] at hq
  have hr' := renameInto hr j Theta hj
  have hb' := renameInto hb j Theta hj
  have hp' := renameInto hp j Theta hj
  have ht' := renameInto ht j Theta hj
  rw [graph1Rename] at hr' hb' hp'
  simp only [graph1Rename,oneRename] at ht'
  let xx : Fin 1 → OTerm beta := Fin.cons (raw.relabel j) Fin.elim0
  have hpv := unaryValue InternalUnpair.right (.projection 0)
    (payload.relabel j) (raw.relabel j) xx hp' (projectionValue 0 xx)
  have hm := unaryRecover InternalUnpair.right rawPayload (ys 0) (payload.relabel j) xx (hq 0) hpv
  have hd := unaryRecover InternalUnpair.left rawMiddle (ys 1) (ys 0) xx (hq 1) (hq 0)
  have hbp := unaryRecover InternalUnpair.right rawMiddle (ys 2) (ys 0) xx (hq 2) (hq 0)
  have htag := unaryRecover InternalUnpair.left rawPayload (numeral 1) (payload.relabel j) xx ht' hpv
  have houter := reconstructPair (payload.relabel j) (numeral 1) (ys 0) htag hm
  have hmiddle := reconstructPair (ys 0) (ys 1) (ys 2) hd hbp
  have hbound := closedApply
    (OriginalHereditaryValidityFuelProof.actualOriginalLambdaPayloadChildFuelBound body beta
      (payload.relabel j) (ys 0) (ys 1) (ys 2)) (andIntro houter hmiddle)
  exact k beta j Theta (ys 2) hj
    (bodyPayloadSelected (state.relabel j) (raw.relabel j) (child.relabel j) (ys 2) hr' hb' (hq 2)) hbound

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceWeightLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceWeightLambdaProof
