module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.BooleanProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.TargetFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTypedDecoder
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem seedGuard (H G : Program 1) (seed param context : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph2 (target H G) (numeral 1) seed param)))
    (hc : Nonempty (Derivation body Delta (graph1 InternalUnpair.left context param))) :
    Nonempty (Derivation body Delta (graph1 G (numeral 1) context)) := by
  have h := InternalAcceptanceConjunctionProof.conjunctionRecover _ _ ![seed,param] ht
  exact unaryRecover G (leftOf (.projection 1)) (numeral 1) context ![seed,param]
    (andLeft h) (unaryValue InternalUnpair.left (.projection 1) context param ![seed,param]
      hc (projectionValue 1 ![seed,param]))

theorem rebuildAt (H G : Program 1) (candidate param typ raw gamma context : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ candidate)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right raw candidate)))
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.right gamma param)))
    (hc : Nonempty (Derivation body Delta (graph1 InternalUnpair.left context param)))
    (hG : Nonempty (Derivation body Delta (graph1 G (numeral 1) context)))
    (hp : Nonempty (Derivation body Delta (graph2 (packedCheck H) (numeral 1) candidate gamma))) :
    Nonempty (Derivation body Delta (graph2 (target H G) (numeral 1) candidate param)) := by
  have hterm : Nonempty (Derivation body Delta (graph3 (termCheck H) (numeral 1) typ raw gamma)) := by
    apply InternalAcceptanceSupportProof.compositionRecover (termCheck H) ![leftOf (.projection 0),rightOf (.projection 0),.projection 1]
      (numeral 1) ![candidate,gamma] ![typ,raw,gamma] hp
    intro i
    exact Fin.cases
      (unaryValue InternalUnpair.left (.projection 0) typ candidate ![candidate,gamma] ht (projectionValue 0 ![candidate,gamma]))
      (Fin.cases (unaryValue InternalUnpair.right (.projection 0) raw candidate ![candidate,gamma] hr (projectionValue 0 ![candidate,gamma]))
        (Fin.cases (projectionValue 1 ![candidate,gamma]) (fun k => Fin.elim0 k))) i
  apply InternalAcceptanceConjunctionProof.conjunctionAccept _ _ ![candidate,param]
  · exact unaryValue G (leftOf (.projection 1)) (numeral 1) context ![candidate,param] hG
      (unaryValue InternalUnpair.left (.projection 1) context param ![candidate,param] hc (projectionValue 1 ![candidate,param]))
  · apply compositionValue (termCheck H) ![leftOf (.projection 0),rightOf (.projection 0),rightOf (.projection 1)]
      (numeral 1) ![candidate,param] ![typ,raw,gamma] hterm
    intro i
    exact Fin.cases
      (unaryValue InternalUnpair.left (.projection 0) typ candidate ![candidate,param] ht (projectionValue 0 ![candidate,param]))
      (Fin.cases (unaryValue InternalUnpair.right (.projection 0) raw candidate ![candidate,param] hr (projectionValue 0 ![candidate,param]))
        (Fin.cases (unaryValue InternalUnpair.right (.projection 1) gamma param ![candidate,param] hg (projectionValue 1 ![candidate,param]))
          (fun k => Fin.elim0 k))) i

theorem rebuild (H G : Program 1) (candidate param gamma context : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.right gamma param)))
    (hc : Nonempty (Derivation body Delta (graph1 InternalUnpair.left context param)))
    (hG : Nonempty (Derivation body Delta (graph1 G (numeral 1) context)))
    (hp : Nonempty (Derivation body Delta (graph2 (packedCheck H) (numeral 1) candidate gamma))) :
    Nonempty (Derivation body Delta (graph2 (target H G) (numeral 1) candidate param)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases
    (![InternalUnpair.left,InternalUnpair.right] : Fin 2 → Program 1) ![candidate] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![candidate] i).relabel j) = ![candidate.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hg' := renameInto hg j Theta hj
  have hc' := renameInto hc j Theta hj
  have hG' := renameInto hG j Theta hj
  have hp' := renameInto hp j Theta hj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hg' hc' hG' hp'
  exact rebuildAt H G (candidate.relabel j) (param.relabel j) (ys 0) (ys 1)
    (gamma.relabel j) (context.relabel j) (hq 0) (hq 1) hg' hc' hG' hp'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.TargetFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.TargetFieldsProof
