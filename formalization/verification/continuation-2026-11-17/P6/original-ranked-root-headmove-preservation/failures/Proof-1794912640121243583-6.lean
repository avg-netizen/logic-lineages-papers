module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.CallerAtSignatureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.HeadIdentityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel eqnRelabel)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalRawSyntaxTransport OriginalUniverseDecoderTransport
open OriginalUniverseDecoderTransportSyntaxProof (acceptedRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
open Continuation20261116.OriginalConcreteHeadSignature

theorem ordinary : Targets.InternalOrdinaryRankedHeadMove := by
  intro n arity M W body alpha Delta left right f g base target typ gamma context symbols windowTypes hlc hrc htag hlg hrg hmove ha
  have hleft := RootGuardProof.ordinary n left f base hlc hlg
  have hright := RootGuardProof.ordinary n right g target hrc hrg
  have hm := (OriginalHeadMove.InternalProof.internalAcceptance n arity body alpha Delta
    f base g target symbols windowTypes).mp hmove
  have he := HeadIdentityProof.rankedEqual f g htag (andRight (andLeft hm))
  have hbg := andRight hleft
  have htg := andRight hright
  have hp := andRight hm
  apply SignatureCasesProof.cases n arity f _ htag (andLeft hleft)
  intro beta j Theta count args packed hj hargs hH hfields
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  rw [graph2Rename] at hlc' hrc'
  have hbg' := renameInto hbg j Theta hj
  have htg' := renameInto htg j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hbg' htg'
  have hp' := renameInto hp j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hp'
  have he' := renameInto he j Theta hj
  rw [eqnRelabel] at he'
  have ha' := renameInto ha j Theta hj
  change Nonempty (Derivation body Theta ((Accepted (signature n arity) M W false typ left gamma context).relabel j)) at ha'
  rw [acceptedRename] at ha'
  change Nonempty (Derivation body Theta ((Accepted (signature n arity) M W false typ right gamma context).relabel j))
  rw [acceptedRename]
  exact CallerAtSignatureProof.ordinary n arity M W
    (left.relabel j) (right.relabel j) (f.relabel j) (g.relabel j) (base.relabel j) (target.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) count args packed
    hlc' hrc' he' hbg' htg' hp' hargs hH hfields ha'

theorem numbered : Targets.InternalNumberedRankedHeadMove := by
  intro n arity M W body alpha Delta left right label f g recorded base target extraTypes extras typ gamma context symbols windowTypes hlc hrc htag hlg hrg hmove ha
  have hleft := RootGuardProof.numbered n left label f recorded base extraTypes extras hlc hlg
  have hright := RootGuardProof.numbered n right label g recorded target extraTypes extras hrc hrg
  have hm := (OriginalHeadMove.InternalProof.internalAcceptance n arity body alpha Delta
    f base g target symbols windowTypes).mp hmove
  have he := HeadIdentityProof.rankedEqual f g htag (andRight (andLeft hm))
  have hbg := andRight hleft
  have htg := andRight hright
  have hp := andRight hm
  apply SignatureCasesProof.cases n arity f _ htag (andLeft hleft)
  intro beta j Theta count args packed hj hargs hH hfields
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  simp only [programRename,OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename] at hlc' hrc'
  have hbg' := renameInto hbg j Theta hj
  have htg' := renameInto htg j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hbg' htg'
  have hp' := renameInto hp j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hp'
  have he' := renameInto he j Theta hj
  rw [eqnRelabel] at he'
  have ha' := renameInto ha j Theta hj
  change Nonempty (Derivation body Theta ((Accepted (signature n arity) M W false typ left gamma context).relabel j)) at ha'
  rw [acceptedRename] at ha'
  change Nonempty (Derivation body Theta ((Accepted (signature n arity) M W false typ right gamma context).relabel j))
  rw [acceptedRename]
  exact CallerAtSignatureProof.numbered n arity M W
    (left.relabel j) (right.relabel j) (label.relabel j) (f.relabel j) (g.relabel j) (recorded.relabel j) (base.relabel j) (target.relabel j) (extraTypes.relabel j) (extras.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) count args packed
    hlc' hrc' he' hbg' htg' hp' hargs hH hfields ha'

theorem rankedRootHeadMoves : Targets.InternalRankedRootHeadMoves := ⟨ordinary,numbered⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.Proof
