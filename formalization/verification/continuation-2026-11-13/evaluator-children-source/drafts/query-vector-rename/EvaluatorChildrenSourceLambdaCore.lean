module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSourceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaSelectorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSourceLambdaCore
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaTraversalInternal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem childAtFields (H G : Program 1) (M W : Program 2)
 (parent parameter d e child arrow bodyParameter : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields parent d e child arrow)))
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) parent parameter)))
 (hb : Nonempty (Derivation body Delta (graph2 OriginalLambdaTraversal.childParameter bodyParameter parent parameter))) :
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) child bodyParameter)) := by
 let cp : Program 2 := leftOf (.projection 1)
 let gp : Program 2 := rightOf (.projection 1)
 let dp : Program 2 := .composition OriginalLambdaTraversal.rawDomain (fun _ : Fin 1 => .projection 0)
 let ep : Program 2 := consOf dp gp
 let qs : Fin 3 → Program 2 := ![cp,gp,ep]
 let xs : Fin 2 → OTerm alpha := ![parent,parameter]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hj hq
 simp only [graph2Rename,SourceComputabilityFormulaSupportProof.numeral,sucRelabel,zRelabel]
 have hf' := renameInto hf j Theta hj
 rw [OriginalLambdaConstructorGraphSyntaxProof.fieldsRename] at hf'
 have hs' : Nonempty (Derivation body Theta
   (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) (parent.relabel j) (parameter.relabel j))) := by
   simpa only [graph2Rename,SourceComputabilityFormulaSupportProof.numeral,sucRelabel,zRelabel] using renameInto hs j Theta hj
 have hb' := renameInto hb j Theta hj
 simp only [graph2Rename,SourceComputabilityFormulaSupportProof.numeral,sucRelabel,zRelabel] at hs' hb'
 simp only [xs,consTermRename,emptyRename] at hq
 let xx : Fin 2 → OTerm beta := ![parent.relabel j,parameter.relabel j]
 have hc := unaryRecover InternalUnpair.left (.projection 1) (ys 0) (parameter.relabel j) xx
   (hq 0) (projectionValue 1 xx)
 have hg := unaryRecover InternalUnpair.right (.projection 1) (ys 1) (parameter.relabel j) xx
   (hq 1) (projectionValue 1 xx)
 have hp := InternalApplicationCertificateConstructorsSupportProof.reconstructPair (parameter.relabel j) (ys 0) (ys 1) hc hg
 have hd := unaryValue OriginalLambdaTraversal.rawDomain (.projection 0) (d.relabel j) (parent.relabel j) xx
   (andLeft (andRight (andRight (andRight hf')))) (projectionValue 0 xx)
 have he := binaryRecover InternalListCodec.consCode dp gp (ys 2) (d.relabel j) (ys 1) xx
   (hq 2) hd (hq 1)
 have hbp := binaryRecover InternalPairing.pairing cp ep (bodyParameter.relabel j) (ys 0) (ys 2) xx
   hb' (hq 0) (hq 2)
 exact OriginalPackedSourceLambdaChildProof.sourceChild H G M W (parent.relabel j) (parameter.relabel j)
   (child.relabel j) (d.relabel j) (e.relabel j) (arrow.relabel j) (ys 0) (ys 1) (ys 2)
   (bodyParameter.relabel j) hf' hs' hp he hbp

theorem bodySelector (parent d e child arrow : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields parent d e child arrow))) :
 Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawBody child parent)) := by
 have hc := InternalListCodecSupportProof.consDestruction arrow d e (andLeft (andRight (andRight hf)))
 have he := unaryValue InternalListCodec.tailCode OriginalLambdaTraversal.rawType e arrow (Fin.cons parent Fin.elim0)
   (andLeft (andRight hc)) (andLeft (andRight hf))
 exact binaryValue OriginalLambdaConstructor.bodyCode OriginalLambdaTraversal.rawCodomain (.projection 0)
   child e parent (Fin.cons parent Fin.elim0) (andRight (andRight (andRight (andRight hf))))
   he (projectionValue 0 (Fin.cons parent Fin.elim0))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSourceLambdaCore
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSourceLambdaCore
