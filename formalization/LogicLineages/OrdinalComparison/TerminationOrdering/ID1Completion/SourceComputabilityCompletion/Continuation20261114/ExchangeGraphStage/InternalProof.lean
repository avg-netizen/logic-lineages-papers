module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphStage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeMapGraph.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphStage.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalOriginalUniformVertexPathSupportProof (ternaryValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem answerGraph (D : Program 2) (G : Program 3) (node old param deps vals value : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 D deps node param)))
    (hm : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph vals deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G value node vals param))) :
    Nonempty (Derivation body Delta (graph3 (nodeAnswer D G) value node old param)) := by
  let xs : Fin 3 → OTerm alpha := ![node,old,param]
  have hd' := binaryValue D (.projection 0) (.projection 2) deps node param xs hd
    (projectionValue 0 xs) (projectionValue 2 xs)
  have hm' := binaryValue ExchangeMapGraph.mapGraph (dependencies D) (.projection 1)
    vals deps old xs hm hd' (projectionValue 1 xs)
  exact ternaryValue G (.projection 0) (answers D) (.projection 2) value node vals param xs
    hg (projectionValue 0 xs) hm' (projectionValue 2 xs)

theorem stepAnswerGraph (D : Program 2) (G : Program 3) (node rest old param value : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph3 (nodeAnswer D G) value node old param))) :
    Nonempty (Derivation body Delta (programGraph (stepAnswer D G) value ![node,rest,old,param])) :=
  ternaryValue (nodeAnswer D G) (.projection 0) (.projection 2) (.projection 3)
    value node old param ![node,rest,old,param] h
    (projectionValue 0 ![node,rest,old,param]) (projectionValue 2 ![node,rest,old,param])
    (projectionValue 3 ![node,rest,old,param])

theorem skipStep (D : Program 2) (G : Program 3) (node rest old param : OTerm alpha)
    (hz : Nonempty (Derivation body Delta (graph3 (nodeAnswer D G) z node old param))) :
    Nonempty (Derivation body Delta (programGraph (step D G) rest ![node,rest,old,param])) :=
  zeroBranchIntro (stepAnswer D G) (.projection 1) _ rest ![node,rest,old,param]
    (stepAnswerGraph D G node rest old param z hz) (projectionValue 1 ![node,rest,old,param])

theorem skipForward (D : Program 2) (G : Program 3) (frontier node tail old param out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode frontier node tail)))
    (hz : Nonempty (Derivation body Delta (graph3 (nodeAnswer D G) z node old param)))
    (hr : Nonempty (Derivation body Delta (graph3 (stage D G) out tail old param))) :
    Nonempty (Derivation body Delta (graph3 (stage D G) out frontier old param)) :=
  InternalRawListRecursionProof.consValue (InternalAcceptance.constantZero 2) (step D G)
    frontier node tail out out (Fin.cons old (Fin.cons param Fin.elim0)) hc hr
    (skipStep D G node out old param hz)

theorem internalSkip : Targets.InternalSkip := by
  intro body alpha Delta D G frontier node tail old param deps vals out hc hd hm hg
  have hz := answerGraph D G node old param deps vals z hd hm hg
  constructor
  · intro h
    apply programCases (stage D G) (Fin.cons tail (Fin.cons old (Fin.cons param Fin.elim0))) _
    intro beta j Theta rest hj hr
    rw [graph3Rename]
    simp only [consTermRename,emptyRename] at hr
    have hc' := renameInto hc j Theta hj
    rw [graph2Rename] at hc'
    have hz' := renameInto hz j Theta hj
    simp only [graph3Rename,zRelabel] at hz'
    have h' := renameInto h j Theta hj
    rw [graph3Rename] at h'
    have hs := skipForward D G (frontier.relabel j) (node.relabel j) (tail.relabel j)
      (old.relabel j) (param.relabel j) rest hc' hz' hr
    have hu := valueUnique (stage D G) rest (out.relabel j)
      ![frontier.relabel j,old.relabel j,param.relabel j] hs h'
    exact outputTransport (stage D G) rest (out.relabel j)
      ![tail.relabel j,old.relabel j,param.relabel j] hu hr
  · exact skipForward D G frontier node tail old param out hc hz

theorem keepStep (D : Program 2) (G : Program 3)
    (node rest old param value pair out : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph3 (nodeAnswer D G) (suc value) node old param)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair node value)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out pair rest))) :
    Nonempty (Derivation body Delta (programGraph (step D G) out ![node,rest,old,param])) := by
  let xs : Fin 4 → OTerm alpha := ![node,rest,old,param]
  have hs := stepAnswerGraph D G node rest old param (suc value) hg
  have hv := unaryValue InternalEqualityTest.predecessor (stepAnswer D G) value (suc value) xs
    (InternalEqualityTestPredecessorProof.predecessorSuccessor value) hs
  have he := binaryValue InternalPairing.pairing (.projection 0)
    (.composition InternalEqualityTest.predecessor (fun _ : Fin 1 => stepAnswer D G))
    pair node value xs hp (projectionValue 0 xs) hv
  have ho := binaryValue InternalListCodec.consCode (entry D G) (.projection 1)
    out pair rest xs hc he (projectionValue 1 xs)
  exact successorBranchIntro (stepAnswer D G) (.projection 1) _ out value xs hs ho

theorem internalKeep : Targets.InternalKeep := by
  intro body alpha Delta D G frontier node tail old param deps vals value pair rest out hc hd hm hg hp hr ho
  have ha := answerGraph D G node old param deps vals (suc value) hd hm hg
  exact InternalRawListRecursionProof.consValue (InternalAcceptance.constantZero 2) (step D G)
    frontier node tail rest out (Fin.cons old (Fin.cons param Fin.elim0)) hc hr
    (keepStep D G node rest old param value pair out ha hp ho)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphStage.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphStage.InternalProof
