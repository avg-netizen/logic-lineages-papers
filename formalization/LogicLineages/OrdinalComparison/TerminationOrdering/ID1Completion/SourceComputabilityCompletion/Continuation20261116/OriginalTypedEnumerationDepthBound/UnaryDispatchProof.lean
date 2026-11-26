module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DispatchFrame
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LambdaBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.OrdinaryBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.SelectorGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportRejectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserUnaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.UnaryDispatchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof (pairLeft)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261115 DispatchFrame
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {n : Nat} {H : Program 1} {arguments : Bool} {body : Positive (Fin 1)}
  {alpha : Type} {Delta : List (Formula alpha)}

theorem lambdaCode (f : Frame n H arguments body alpha Delta) (payload first : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing f.raw (numeral 1) payload)))
    (hf : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) first f.raw)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) first))) :
    Nonempty (Derivation body Delta f.conclusion) := by
  cases arguments
  · apply OriginalRawSyntaxTransportInternalParserUnaryProof.lambdaCases f.raw f.conclusion
      (pairLeft f.raw (numeral 1) payload hp)
    intro beta j Theta metadata child hj hc
    rw [conclusionRename f j Theta hj]
    let fj := f.rename j Theta hj
    have hfj := renameInto hf j Theta hj
    have hgj := renameInto hg j Theta hj
    simp only [graph1Rename,sucRelabel,zRelabel] at hfj hgj
    have hchild := SelectorGuardProof.lambdaCode n fj.raw metadata child (first.relabel j) hc hfj hgj
    exact LambdaBranchProof.atConstructor n H fj.raw metadata child fj.typ fj.gamma fj.pair fj.size fj.label fj.depth
      hc fj.guard hchild fj.typed fj.bounds fj.paired fj.measured fj.ih
  · exact OriginalTypedDecoderTransportRejectedProof.argumentsOther H 1 (by decide) (by decide)
      f.raw payload f.typ f.gamma f.conclusion hp f.typed

theorem ordinary (f : Frame n H arguments body alpha Delta) (payload first : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing f.raw (numeral 4) payload)))
    (hf : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) first f.raw)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) first))) :
    Nonempty (Derivation body Delta f.conclusion) := by
  cases arguments
  · apply OriginalRawSyntaxTransportInternalParserUnaryProof.ordinaryCases f.raw f.conclusion
      (pairLeft f.raw (numeral 4) payload hp)
    intro beta j Theta metadata child hj hc
    rw [conclusionRename f j Theta hj]
    let fj := f.rename j Theta hj
    have hfj := renameInto hf j Theta hj
    have hgj := renameInto hg j Theta hj
    simp only [graph1Rename,sucRelabel,zRelabel] at hfj hgj
    have hchild := SelectorGuardProof.ordinary n fj.raw metadata child (first.relabel j) hc hfj hgj
    exact OrdinaryBranchProof.atConstructor n H fj.raw metadata child fj.typ fj.gamma fj.pair fj.size fj.label fj.depth
      hc fj.guard hchild fj.typed fj.bounds fj.paired fj.measured fj.ih
  · exact OriginalTypedDecoderTransportRejectedProof.argumentsOther H 4 (by decide) (by decide)
      f.raw payload f.typ f.gamma f.conclusion hp f.typed
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.UnaryDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.UnaryDispatchProof
