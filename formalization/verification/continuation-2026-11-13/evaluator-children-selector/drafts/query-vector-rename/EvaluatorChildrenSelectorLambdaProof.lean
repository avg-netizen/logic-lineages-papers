module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSelectorWiring
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaSelectorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSelectorLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open EvaluatorChildrenSelectorWiring

theorem bodyAt (parent parameter e child : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawCodomain e parent)))
 (hb : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawBody child parent))) :
 Nonempty (Derivation body Delta (graph2 OriginalRootObservation.bodyPacked child parent parameter)) := by
 apply programCases OriginalLambdaConstructor.bodyPayload (Fin.cons parent Fin.elim0) _
 intro beta j Theta raw hj hr
 rw [graph2Rename]
 simp only [consTermRename,emptyRename] at hr
 have he' := renameInto he j Theta hj
 have hb' := renameInto hb j Theta hj
 rw [graph1Rename] at he' hb'
 have hp := OriginalLambdaConstructorGraphSupportProof.bodyCodeRecover
   (child.relabel j) (e.relabel j) (parent.relabel j) raw
   (OriginalLambdaTraversalLambdaSelectorProof.bodyCodeAt (parent.relabel j) (e.relabel j) (child.relabel j) he' hb') hr
 exact binaryValue InternalPairing.pairing OriginalRootObservation.codomain (rightOf OriginalRootObservation.payload)
   (child.relabel j) (e.relabel j) raw ![parent.relabel j,parameter.relabel j] hp
   (codomain body beta Theta (e.relabel j) (parent.relabel j) (parameter.relabel j) he')
   (bodyPayload body beta Theta raw (parent.relabel j) (parameter.relabel j) hr)

theorem parameterAt (parent parameter d bodyParameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawDomain d parent)))
 (hb : Nonempty (Derivation body Delta (graph2 OriginalLambdaTraversal.childParameter bodyParameter parent parameter))) :
 Nonempty (Derivation body Delta (graph2 OriginalRootObservation.childParameter bodyParameter parent parameter)) := by
 let cp : Program 2 := leftOf (.projection 1)
 let gp : Program 2 := rightOf (.projection 1)
 let dp : Program 2 := .composition OriginalLambdaTraversal.rawDomain (fun _ : Fin 1 => .projection 0)
 let ep : Program 2 := consOf dp gp
 let qs : Fin 3 → Program 2 := ![cp,gp,ep]
 let xs : Fin 2 → OTerm alpha := ![parent,parameter]
 apply queryCases qs xs _
 intro beta j ys Theta hj hq
 rw [graph2Rename]
 have hd' := renameInto hd j Theta hj
 rw [graph1Rename] at hd'
 have hb' := renameInto hb j Theta hj
 rw [graph2Rename] at hb'
 simp only [xs,consTermRename,emptyRename] at hq
 let xx : Fin 2 → OTerm beta := ![parent.relabel j,parameter.relabel j]
 have hdp := unaryValue OriginalLambdaTraversal.rawDomain (.projection 0) (d.relabel j) (parent.relabel j) xx hd' (projectionValue 0 xx)
 have he := binaryRecover InternalListCodec.consCode dp gp (ys 2) (d.relabel j) (ys 1) xx (hq 2) hdp (hq 1)
 have hp := binaryRecover InternalPairing.pairing cp ep (bodyParameter.relabel j) (ys 0) (ys 2) xx hb' (hq 0) (hq 2)
 have hnew := binaryValue InternalListCodec.consCode OriginalRootObservation.domain gp
   (ys 2) (d.relabel j) (ys 1) xx he
   (domain body beta Theta (d.relabel j) (parent.relabel j) (parameter.relabel j) hd') (hq 1)
 exact binaryValue InternalPairing.pairing cp (consOf OriginalRootObservation.domain gp)
   (bodyParameter.relabel j) (ys 0) (ys 2) xx hp (hq 0) hnew

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSelectorLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSelectorLambdaProof
