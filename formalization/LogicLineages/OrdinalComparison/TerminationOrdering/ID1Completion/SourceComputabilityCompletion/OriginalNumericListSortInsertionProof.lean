module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortOriginalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortInsertionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalRecursionClosureLogicProof (closedApply)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open OriginalNumericListSort
open OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof (unaryVectorRename binaryVectorRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem statePair (raw x state out : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 insertState state raw x)))
 (ho : Nonempty (Derivation body Delta (graph2 insert out raw x))) :
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw out)) := by
 have hl := closedApply (OriginalNumericListSortOriginalProof.originalCoordinate body alpha raw x state) hs
 have hr := unaryRecover InternalUnpair.right insertState out state ![raw,x] ho hs
 exact closedApply (InternalUnpairReverseProof.actualOriginalUnpairReverseInverse body alpha state raw out)
   (andIntro hl hr)

theorem insertionCases (raw x : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta)) (state out : OTerm beta),
   (∀ p ∈ Delta, p.relabel rho ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 insertState state (raw.relabel rho) (x.relabel rho))) →
   Nonempty (Derivation body Theta (graph2 insert out (raw.relabel rho) (x.relabel rho))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing state (raw.relabel rho) out)) →
   Nonempty (Derivation body Theta (psi.relabel rho))) :
 Nonempty (Derivation body Delta psi) := by
 apply programCases insertState ![raw,x] _
 intro beta rho Theta state hrho hs
 rw [binaryVectorRename] at hs
 apply programCases InternalUnpair.right ![state] _
 intro gamma eta Xi out heta ho
 rw [unaryVectorRename] at ho
 have hs' := renameInto hs eta Xi heta
 rw [programRename,binaryVectorRename] at hs'
 have hv := unaryValue InternalUnpair.right insertState out (state.relabel eta)
   ![(raw.relabel rho).relabel eta,(x.relabel rho).relabel eta] ho hs'
 have hp := statePair ((raw.relabel rho).relabel eta) ((x.relabel rho).relabel eta) (state.relabel eta) out hs' hv
 have hctx : ∀ p ∈ Delta, p.relabel (eta ∘ rho) ∈ Xi := by
   intro p h
   simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using heta (p.relabel rho) (hrho p h)
 simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition,Term.relabel_relabel] using
   next gamma (eta ∘ rho) Xi (state.relabel eta) out hctx hs' hv hp

theorem beforeAtState (raw head tail x out previous inserted state : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (ht : Nonempty (Derivation body Delta (graph2 insertState previous tail x)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing previous tail inserted)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out x raw)))
 (hlt : Nonempty (Derivation body Delta (graph2 InternalLessThan.ltTest z head x)))
 (hstate : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw out))) :
 Nonempty (Derivation body Delta (graph2 insert out raw x)) := by
 have hstep := OriginalNumericListSortValueProof.stepBefore head tail inserted previous raw x out state hp hc ho hstate hlt
 have hs := InternalRawListRecursionProof.consValue insertBase insertStep raw head tail previous state (Fin.cons x Fin.elim0) hc ht hstep
 exact OriginalNumericListSortValueProof.insertFromState raw x state out hs hstate

theorem beforeAtTail (raw head tail x out previous inserted : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (ht : Nonempty (Derivation body Delta (graph2 insertState previous tail x)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing previous tail inserted)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out x raw)))
 (hlt : Nonempty (Derivation body Delta (graph2 InternalLessThan.ltTest z head x))) :
 Nonempty (Derivation body Delta (graph2 insert out raw x)) := by
 apply programCases InternalPairing.pairing ![raw,out] _
 intro beta rho Theta state hrho hs
 rw [binaryVectorRename] at hs
 simp only [graph2Rename]
 have hc' := renameInto hc rho Theta hrho
 simp only [graph2Rename,zRelabel,sucRelabel] at hc'
 have ht' := renameInto ht rho Theta hrho
 simp only [graph2Rename,zRelabel,sucRelabel] at ht'
 have hp' := renameInto hp rho Theta hrho
 simp only [graph2Rename,zRelabel,sucRelabel] at hp'
 have ho' := renameInto ho rho Theta hrho
 simp only [graph2Rename,zRelabel,sucRelabel] at ho'
 have hlt' := renameInto hlt rho Theta hrho
 simp only [graph2Rename,zRelabel,sucRelabel] at hlt'
 exact beforeAtState (raw.relabel rho) (head.relabel rho) (tail.relabel rho) (x.relabel rho)
   (out.relabel rho) (previous.relabel rho) (inserted.relabel rho) state hc' ht' hp' ho' hlt' hs

theorem afterAtState (raw head tail x out previous inserted state : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (ht : Nonempty (Derivation body Delta (graph2 insertState previous tail x)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing previous tail inserted)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out head inserted)))
 (hlt : Nonempty (Derivation body Delta (graph2 InternalLessThan.ltTest (suc z) head x)))
 (hstate : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw out))) :
 Nonempty (Derivation body Delta (graph2 insert out raw x)) := by
 have hstep := OriginalNumericListSortValueProof.stepAfter head tail inserted previous raw x out state z hp hc ho hstate hlt
 have hs := InternalRawListRecursionProof.consValue insertBase insertStep raw head tail previous state (Fin.cons x Fin.elim0) hc ht hstep
 exact OriginalNumericListSortValueProof.insertFromState raw x state out hs hstate

theorem afterAtTail (raw head tail x out previous inserted : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (ht : Nonempty (Derivation body Delta (graph2 insertState previous tail x)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing previous tail inserted)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out head inserted)))
 (hlt : Nonempty (Derivation body Delta (graph2 InternalLessThan.ltTest (suc z) head x))) :
 Nonempty (Derivation body Delta (graph2 insert out raw x)) := by
 apply programCases InternalPairing.pairing ![raw,out] _
 intro beta rho Theta state hrho hs
 rw [binaryVectorRename] at hs
 simp only [graph2Rename]
 have hc' := renameInto hc rho Theta hrho
 simp only [graph2Rename,zRelabel,sucRelabel] at hc'
 have ht' := renameInto ht rho Theta hrho
 simp only [graph2Rename,zRelabel,sucRelabel] at ht'
 have hp' := renameInto hp rho Theta hrho
 simp only [graph2Rename,zRelabel,sucRelabel] at hp'
 have ho' := renameInto ho rho Theta hrho
 simp only [graph2Rename,zRelabel,sucRelabel] at ho'
 have hlt' := renameInto hlt rho Theta hrho
 simp only [graph2Rename,zRelabel,sucRelabel] at hlt'
 exact afterAtState (raw.relabel rho) (head.relabel rho) (tail.relabel rho) (x.relabel rho)
   (out.relabel rho) (previous.relabel rho) (inserted.relabel rho) state hc' ht' hp' ho' hlt' hs

theorem beforeValue (raw head tail x out : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out x raw)))
 (hlt : Nonempty (Derivation body Delta (ltF head x).not)) :
 Nonempty (Derivation body Delta (graph2 insert out raw x)) := by
 have htest := InternalLessThanSupportProof.rejectOfNotLess head x hlt
 apply insertionCases tail x _
 intro beta rho Theta previous inserted hrho ht _ hp
 simp only [graph2Rename]
 have hc' := renameInto hc rho Theta hrho
 have ho' := renameInto ho rho Theta hrho
 have htest' := renameInto htest rho Theta hrho
 simp only [graph2Rename] at hc' ho'
 simp only [InternalLessThanSupportProof.lessGraphRename,zRelabel] at htest'
 exact beforeAtTail (raw.relabel rho) (head.relabel rho) (tail.relabel rho) (x.relabel rho)
   (out.relabel rho) previous inserted hc' ht hp ho' htest'

theorem afterValue (raw head tail x inserted out : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hi : Nonempty (Derivation body Delta (graph2 insert inserted tail x)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out head inserted)))
 (hlt : Nonempty (Derivation body Delta (ltF head x))) :
 Nonempty (Derivation body Delta (graph2 insert out raw x)) := by
 have htest := InternalLessThanSupportProof.acceptOfLess head x hlt
 apply programCases insertState ![tail,x] _
 intro beta rho Theta previous hrho ht
 rw [binaryVectorRename] at ht
 simp only [graph2Rename]
 have hc' := renameInto hc rho Theta hrho
 have hi' := renameInto hi rho Theta hrho
 have ho' := renameInto ho rho Theta hrho
 have htest' := renameInto htest rho Theta hrho
 simp only [graph2Rename] at hc' hi' ho'
 simp only [InternalLessThanSupportProof.lessGraphRename,zRelabel,sucRelabel] at htest'
 have hp := statePair (tail.relabel rho) (x.relabel rho) previous (inserted.relabel rho) ht hi'
 exact afterAtTail (raw.relabel rho) (head.relabel rho) (tail.relabel rho) (x.relabel rho)
   (out.relabel rho) previous (inserted.relabel rho) hc' ht hp ho' htest'

theorem nilValue (x out : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out x z))) :
 Nonempty (Derivation body Delta (graph2 insert out z x)) := by
 apply programCases InternalPairing.pairing ![z,out] _
 intro beta rho Theta state hrho hp
 rw [binaryVectorRename] at hp
 simp only [zRelabel] at hp
 simp only [graph2Rename,zRelabel]
 have hc' := renameInto hc rho Theta hrho
 simp only [graph2Rename,zRelabel] at hc'
 exact OriginalNumericListSortValueProof.insertNil (x.relabel rho) (out.relabel rho) state hc' hp

theorem nilRecover (x out : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (graph2 insert out z x))) :
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out x z)) := by
 apply programCases InternalListCodec.consCode ![x,z] _
 intro beta rho Theta v hrho hc
 rw [binaryVectorRename] at hc
 simp only [zRelabel] at hc
 simp only [graph2Rename,zRelabel]
 have hi' := renameInto hi rho Theta hrho
 simp only [graph2Rename,zRelabel] at hi'
 have hv := nilValue (x.relabel rho) v hc
 exact outputTransport InternalListCodec.consCode v (out.relabel rho) ![x.relabel rho,z]
   (valueUnique insert v (out.relabel rho) ![z,x.relabel rho] hv hi') hc

theorem beforeRecover (raw head tail x out : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hi : Nonempty (Derivation body Delta (graph2 insert out raw x)))
 (hlt : Nonempty (Derivation body Delta (ltF head x).not)) :
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out x raw)) := by
 apply programCases InternalListCodec.consCode ![x,raw] _
 intro beta rho Theta v hrho hv
 rw [binaryVectorRename] at hv
 simp only [graph2Rename]
 have hc' := renameInto hc rho Theta hrho
 have hi' := renameInto hi rho Theta hrho
 have hl' := renameInto hlt rho Theta hrho
 simp only [graph2Rename] at hc' hi'
 simp only [OriginalTypedDecoderTransportLogicalProof.notRename,orderRename] at hl'
 have h := beforeValue (raw.relabel rho) (head.relabel rho) (tail.relabel rho) (x.relabel rho) v hc' hv hl'
 exact outputTransport InternalListCodec.consCode v (out.relabel rho) ![x.relabel rho,raw.relabel rho]
   (valueUnique insert v (out.relabel rho) ![raw.relabel rho,x.relabel rho] h hi') hv

theorem afterRecover (raw head tail x inserted out : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (ht : Nonempty (Derivation body Delta (graph2 insert inserted tail x)))
 (hi : Nonempty (Derivation body Delta (graph2 insert out raw x)))
 (hlt : Nonempty (Derivation body Delta (ltF head x))) :
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out head inserted)) := by
 apply programCases InternalListCodec.consCode ![head,inserted] _
 intro beta rho Theta v hrho hv
 rw [binaryVectorRename] at hv
 simp only [graph2Rename]
 have hc' := renameInto hc rho Theta hrho
 have ht' := renameInto ht rho Theta hrho
 have hi' := renameInto hi rho Theta hrho
 have hl' := renameInto hlt rho Theta hrho
 simp only [graph2Rename] at hc' ht' hi'
 simp only [orderRename] at hl'
 have h := afterValue (raw.relabel rho) (head.relabel rho) (tail.relabel rho) (x.relabel rho)
   (inserted.relabel rho) v hc' ht' hv hl'
 exact outputTransport InternalListCodec.consCode v (out.relabel rho) ![head.relabel rho,inserted.relabel rho]
   (valueUnique insert v (out.relabel rho) ![raw.relabel rho,x.relabel rho] h hi') hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortInsertionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortInsertionProof
