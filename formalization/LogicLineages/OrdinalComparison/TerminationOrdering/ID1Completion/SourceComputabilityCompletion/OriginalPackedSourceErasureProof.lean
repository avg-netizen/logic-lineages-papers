module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportInterfaceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalPackedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open InternalAcceptanceSupportProof
open InternalGraphComposition InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalRawSyntaxTransport
open OriginalTransparentDecoderValidatorCollapsePackedProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Glue at literal pairs. G is copied from original source acceptance and
all H/M/W/type metadata remain exactly the same. -/
theorem atCoordinates (H G : Program 1) (M W : Program 2)
 (packed out typ raw erased d cutoff gamma extended c oldParam newParam : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (he : Nonempty (Derivation body Delta (graph3 eraseRaw erased d cutoff raw)))
 (hi : Nonempty (Derivation body Delta (OriginalContextInsertion.Insert d cutoff gamma extended)))
 (ho : Nonempty (Derivation body Delta (graph3 erasePackedRaw out d cutoff packed)))
 (hop : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing oldParam c extended)))
 (hnp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newParam c gamma)))
 (hs : Nonempty (Derivation body Delta
   (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed oldParam))) :
 Nonempty (Derivation body Delta
   (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) out newParam)) := by
 have hf := sourceFieldsElim H G M W packed oldParam typ raw c extended hp hop hs
 have ha := OriginalUniverseDecoderTransportInterfaceProof.erasureAt H M W false
   d cutoff gamma extended typ raw erased c
   (OriginalUniverseDecoderTransportInductionProof.allRawTransport H M W true raw) hi he (andRight hf)
 have hout := OriginalRawSyntaxTransportInternalPackedProof.erasePackedForward
   packed out typ raw erased d cutoff hp he ho
 exact sourceFieldsIntro H G M W out newParam typ erased c gamma hout hnp (andLeft hf) ha

theorem actualOriginalPackedSourceErasure :
 OriginalPackedSourceErasureTargets.ActualOriginalPackedSourceErasure := by
 intro body alpha Delta H G M W packed out d cutoff gamma extended c oldParam newParam hi ho hop hnp hs
 let qs : Fin 3 → Program 3 := ![leftOf (.projection 2),rightOf (.projection 2),
   .composition eraseRaw ![.projection 0,.projection 1,rightOf (.projection 2)] ]
 let xs : Fin 3 → OTerm alpha := Fin.cons d (Fin.cons cutoff (Fin.cons packed Fin.elim0))
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hj hq
 simp only [graph2Rename, GuardedSourceSyntaxProof.numeralRename]
 have hi' := renameInto hi j Theta hj
 rw [OriginalContextInsertionSyntaxProof.insertRename] at hi'
 have ho' := renameInto ho j Theta hj
 rw [graph3Rename] at ho'
 have hop' := renameInto hop j Theta hj
 rw [graph2Rename] at hop'
 have hnp' := renameInto hnp j Theta hj
 rw [graph2Rename] at hnp'
 have hs' := renameInto hs j Theta hj
 simp only [graph2Rename, GuardedSourceSyntaxProof.numeralRename] at hs'
 let xx : Fin 3 → OTerm beta := Fin.cons (d.relabel j) (Fin.cons (cutoff.relabel j) (Fin.cons (packed.relabel j) Fin.elim0))
 have hq' : ∀ i, Nonempty (Derivation body Theta (programGraph (qs i) (ys i) xx)) := by
   intro i
   simpa only [xs,xx,InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] using hq i
 have hl := unaryRecover InternalUnpair.left (.projection 2) (ys 0) (packed.relabel j) xx
   (hq' 0) (projectionValue 2 xx)
 have hr := unaryRecover InternalUnpair.right (.projection 2) (ys 1) (packed.relabel j) xx
   (hq' 1) (projectionValue 2 xx)
 have hp := reconstructPair (packed.relabel j) (ys 0) (ys 1) hl hr
 have he : Nonempty (Derivation body Theta
   (graph3 eraseRaw (ys 2) (d.relabel j) (cutoff.relabel j) (ys 1))) := by
   refine compositionRecover eraseRaw ![.projection 0,.projection 1,rightOf (.projection 2)]
     (ys 2) xx (Fin.cons (d.relabel j) (Fin.cons (cutoff.relabel j) (Fin.cons (ys 1) Fin.elim0))) (hq' 2) ?_
   intro i
   exact Fin.cases (projectionValue 0 xx) (Fin.cases (projectionValue 1 xx)
     (Fin.cases (hq' 1) (fun k => Fin.elim0 k))) i
 exact atCoordinates H G M W (packed.relabel j) (out.relabel j) (ys 0) (ys 1) (ys 2)
   (d.relabel j) (cutoff.relabel j) (gamma.relabel j) (extended.relabel j) (c.relabel j)
   (oldParam.relabel j) (newParam.relabel j) hp he hi' ho' hop' hnp' hs'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureProof
