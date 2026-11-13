module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyConditionalCancellationCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyConditionalCancellationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalRawSyntaxTransport (constant)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open UniformCertificateCompletion EvaluatorKeyPut
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof

theorem actualConditionalCancellation : EvaluatorKeyConditionalCancellationTargets.ActualConditionalCancellation := by
 intro p H G W P body alpha Delta input raw gamma context parameter d shifted canonicalShift erased erasedRaw out originalOut
   hp hpp hd hs hk he hr hSame ho hor
 let C : Program 5 := .composition InternalListCodec.consCode ![.projection 0,.projection 1]
 let T : Program 5 := .composition OriginalRawSyntaxTransport.shiftPackedRaw ![constant 5 0,.projection 2]
 let EP : Program 5 := .composition InternalPairing.pairing ![.projection 3,C]
 let CR : Program 5 := .composition InternalUnpair.right (fun _ : Fin 1 => .projection 4)
 let EQ : Program 5 := .composition OriginalRawObjectTransportInternalSupportProof.erasedPayload (fun _ : Fin 1 => .projection 4)
 let qs : Fin 5 → Program 5 := ![C,T,EP,CR,EQ]
 let xs : Fin 5 → OTerm alpha := ![d,gamma,raw,context,canonicalShift]
 apply OriginalRawSyntaxTransportInternalParserSupportProof.programsCases qs xs _
 intro beta j Theta values hj hg
 have hx : (fun i => (xs i).relabel j) =
     (![d.relabel j,gamma.relabel j,raw.relabel j,context.relabel j,canonicalShift.relabel j] : Fin 5 → OTerm beta) := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))) i
 rw [hx] at hg
 let xx : Fin 5 → OTerm beta := ![d.relabel j,gamma.relabel j,raw.relabel j,context.relabel j,canonicalShift.relabel j]
 have hc := binaryRecover InternalListCodec.consCode (.projection 0) (.projection 1)
   (values 0) (d.relabel j) (gamma.relabel j) xx (hg 0) (projectionValue 0 xx) (projectionValue 1 xx)
 have ht := binaryRecover OriginalRawSyntaxTransport.shiftPackedRaw (constant 5 0) (.projection 2)
   (values 1) (numeral 0) (raw.relabel j) xx (hg 1) (constantValue 0 xx) (projectionValue 2 xx)
 have hep := binaryRecover InternalPairing.pairing (.projection 3) C
   (values 2) (context.relabel j) (values 0) xx (hg 2) (projectionValue 3 xx) (hg 0)
 have hcr := unaryRecover InternalUnpair.right (.projection 4)
   (values 3) (canonicalShift.relabel j) xx (hg 3) (projectionValue 4 xx)
 have heq := unaryRecover OriginalRawObjectTransportInternalSupportProof.erasedPayload (.projection 4)
   (values 4) (canonicalShift.relabel j) xx (hg 4) (projectionValue 4 xx)
 have hp' := renameInto hp j Theta hj
 have hpp' := renameInto hpp j Theta hj
 have hd' := renameInto hd j Theta hj
 have hs' := renameInto hs j Theta hj
 have hk' := renameInto hk j Theta hj
 have he' := renameInto he j Theta hj
 have hr' := renameInto hr j Theta hj
 have hSame' := renameInto hSame j Theta hj
 have ho' := renameInto ho j Theta hj
 have hor' := renameInto hor j Theta hj
 rw [graph2Rename] at hp' hpp' hs' hk' ho' hor'
 rw [graph1Rename] at he' hr'
 simp only [Domain,OriginalActiveKernelMinimumSupportProof.domainRename] at hd'
 simp only [Same,SixSol20261113.Erasure.EvaluatorErasureSyntax.sameRename] at hSame'
 rw [equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel,← equalEqn]
 exact EvaluatorKeyConditionalCancellationCoreProof.atCoordinates p H G W P
   (input.relabel j) (raw.relabel j) (gamma.relabel j) (context.relabel j) (parameter.relabel j)
   (d.relabel j) (shifted.relabel j) (canonicalShift.relabel j) (erased.relabel j) (erasedRaw.relabel j)
   (out.relabel j) (originalOut.relabel j) (values 0) (values 1) (values 2) (values 3) (values 4)
   hp' hpp' hd' hs' hk' he' hr' hSame' ho' hor' hc ht hep hcr heq
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyConditionalCancellationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyConditionalCancellationProof
