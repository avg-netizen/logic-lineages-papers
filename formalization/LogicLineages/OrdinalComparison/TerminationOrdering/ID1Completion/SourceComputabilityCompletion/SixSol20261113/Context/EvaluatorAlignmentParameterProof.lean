module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSelectorWiring
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaSelectorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentParameterProof
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

theorem commonDomain (left right parameter domain lp rp : OTerm alpha)
 (hdl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.domain domain left parameter)))
 (hdr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.domain domain right parameter)))
 (hpl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.childParameter lp left parameter)))
 (hpr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.childParameter rp right parameter))) :
 Nonempty (Derivation body Delta (equal lp rp)) := by
 let cp : Program 2 := leftOf (.projection 1)
 let gp : Program 2 := rightOf (.projection 1)
 let ep : Program 2 := consOf OriginalRootObservation.domain gp
 let qs : Fin 3 → Program 2 := ![cp,gp,ep]
 let xs : Fin 2 → OTerm alpha := ![left,parameter]
 apply queryCases qs xs _
 intro beta j ys Theta hj hq
 have hx : (fun i => (xs i).relabel j) = (![left.relabel j,parameter.relabel j] : Fin 2 → OTerm beta) := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hq
 let xx : Fin 2 → OTerm beta := ![left.relabel j,parameter.relabel j]
 let yy : Fin 2 → OTerm beta := ![right.relabel j,parameter.relabel j]
 have hdl' := renameInto hdl j Theta hj
 have hdr' := renameInto hdr j Theta hj
 have hpl' := renameInto hpl j Theta hj
 have hpr' := renameInto hpr j Theta hj
 rw [graph2Rename] at hdl' hdr' hpl' hpr'
 have hc := unaryRecover InternalUnpair.left (.projection 1) (ys 0) (parameter.relabel j) xx (hq 0) (projectionValue 1 xx)
 have hg := unaryRecover InternalUnpair.right (.projection 1) (ys 1) (parameter.relabel j) xx (hq 1) (projectionValue 1 xx)
 have he := binaryRecover InternalListCodec.consCode OriginalRootObservation.domain gp (ys 2)
   (domain.relabel j) (ys 1) xx (hq 2) hdl' (hq 1)
 have hcr := unaryValue InternalUnpair.left (.projection 1) (ys 0) (parameter.relabel j) yy hc (projectionValue 1 yy)
 have hgr := unaryValue InternalUnpair.right (.projection 1) (ys 1) (parameter.relabel j) yy hg (projectionValue 1 yy)
 have her := binaryValue InternalListCodec.consCode OriginalRootObservation.domain gp (ys 2)
   (domain.relabel j) (ys 1) yy he hdr' hgr
 have hl := binaryRecover InternalPairing.pairing cp ep (lp.relabel j) (ys 0) (ys 2) xx hpl' (hq 0) (hq 2)
 have hr := binaryRecover InternalPairing.pairing cp ep (rp.relabel j) (ys 0) (ys 2) yy hpr' hcr her
 rw [equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel]
 exact valueUnique InternalPairing.pairing (lp.relabel j) (rp.relabel j) (![ys 0,ys 2]) hl hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentParameterProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentParameterProof
