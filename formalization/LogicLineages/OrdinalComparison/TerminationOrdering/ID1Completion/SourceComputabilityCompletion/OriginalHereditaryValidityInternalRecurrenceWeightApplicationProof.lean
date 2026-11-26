module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceWeightSelectorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceWeightApplicationProof
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
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def rawPayload : Program 1 := rightOf (.projection 0)
def rawMiddle : Program 1 := rightOf rawPayload
def rawChildren : Program 1 := rightOf rawMiddle

/-- The bound is derived from the original three payload pair graphs.
All witnesses are internally selected, and both reconstructed children are
connected to the actual machine selectors at the same state. -/
 theorem applicationPayloadCases (state raw fn arg payload : OTerm alpha) (psi : Formula alpha)
    (hr : Nonempty (Derivation body Delta (graph1 currentRaw raw state)))
    (hf : Nonempty (Derivation body Delta (graph1 currentFunction fn state)))
    (ha : Nonempty (Derivation body Delta (graph1 currentArgument arg state)))
    (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload raw)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 2) raw)))
    (k : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (fp ap : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 InternalUnpair.right fp (fn.relabel j))) →
      Nonempty (Derivation body Theta (graph1 InternalUnpair.right ap (arg.relabel j))) →
      Nonempty (Derivation body Theta (weakBound (childFuelSum fp ap) (payload.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let qs : Fin 5 → Program 1 := ![rawMiddle,rawChildren,leftOf rawMiddle,
    leftOf rawChildren,rightOf rawChildren]
  let xs : Fin 1 → OTerm alpha := Fin.cons raw Fin.elim0
  apply queryCases qs xs psi
  intro beta j ys Theta hj hq
  simp only [xs,consTermRename,emptyRename] at hq
  have hr' := renameInto hr j Theta hj
  have hf' := renameInto hf j Theta hj
  have ha' := renameInto ha j Theta hj
  have hp' := renameInto hp j Theta hj
  have ht' := renameInto ht j Theta hj
  rw [graph1Rename] at hr' hf' ha' hp'
  simp only [graph1Rename,SourceComputabilityFormulaSupportProof.numeral,
    sucRelabel,zRelabel] at ht'
  let xx : Fin 1 → OTerm beta := Fin.cons (raw.relabel j) Fin.elim0
  have hpv := unaryValue InternalUnpair.right (.projection 0)
    (payload.relabel j) (raw.relabel j) xx hp' (projectionValue 0 xx)
  have hm := unaryRecover InternalUnpair.right rawPayload (ys 0) (payload.relabel j) xx (hq 0) hpv
  have hc := unaryRecover InternalUnpair.right rawMiddle (ys 1) (ys 0) xx (hq 1) (hq 0)
  have hd := unaryRecover InternalUnpair.left rawMiddle (ys 2) (ys 0) xx (hq 2) (hq 0)
  have hfp := unaryRecover InternalUnpair.left rawChildren (ys 3) (ys 1) xx (hq 3) (hq 1)
  have hap := unaryRecover InternalUnpair.right rawChildren (ys 4) (ys 1) xx (hq 4) (hq 1)
  have htag := unaryRecover InternalUnpair.left rawPayload (numeral 2) (payload.relabel j) xx ht' hpv
  have houter := reconstructPair (payload.relabel j) (numeral 2) (ys 0) htag hm
  have hmiddle := reconstructPair (ys 0) (ys 2) (ys 1) hd hc
  have hchildren := reconstructPair (ys 1) (ys 3) (ys 4) hfp hap
  have hbound := closedApply
    (InternalPairingSumBoundsProof.actualOriginalApplicationPayloadChildFuelBound body beta
      (payload.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4))
    (andIntro houter (andIntro hmiddle hchildren))
  have hstatePayload := unaryValue InternalUnpair.right currentRaw
    (payload.relabel j) (raw.relabel j) (Fin.cons (state.relabel j) Fin.elim0) hp' hr'
  exact k beta j Theta (ys 3) (ys 4) hj
    (functionPayloadSelected (state.relabel j) (fn.relabel j) (payload.relabel j)
      (ys 0) (ys 1) (ys 3) hf' hstatePayload hm hc hfp)
    (argumentPayloadSelected (state.relabel j) (arg.relabel j) (payload.relabel j)
      (ys 0) (ys 1) (ys 4) ha' hstatePayload hm hc hap) hbound

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceWeightApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceWeightApplicationProof
