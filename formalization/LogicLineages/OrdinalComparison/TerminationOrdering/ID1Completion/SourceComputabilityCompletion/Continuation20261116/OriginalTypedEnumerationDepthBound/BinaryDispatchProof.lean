module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DispatchFrame
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ApplicationBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ConsBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.SelectorGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportRejectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserBinaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.BinaryDispatchProof
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

theorem application (f : Frame n H arguments body alpha Delta) (payload first second : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing f.raw (numeral 2) payload)))
    (hf : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) first f.raw)))
    (hs : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.secondOf (.projection 0)) second f.raw)))
    (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) first)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) second))) :
    Nonempty (Derivation body Delta f.conclusion) := by
  cases arguments
  · apply OriginalRawSyntaxTransportInternalParserBinaryProof.applicationCases f.raw f.conclusion
      (pairLeft f.raw (numeral 2) payload hp)
    intro beta j Theta domain left right hj hc
    rw [conclusionRename f j Theta hj]
    let fj := f.rename j Theta hj
    have hfj := renameInto hf j Theta hj
    have hsj := renameInto hs j Theta hj
    have hlgj := renameInto hlg j Theta hj
    have hrgj := renameInto hrg j Theta hj
    simp only [graph1Rename,sucRelabel,zRelabel] at hfj hsj hlgj hrgj
    obtain ⟨hl,hr⟩ := SelectorGuardProof.application n fj.raw domain left right (first.relabel j) (second.relabel j)
      hc hfj hsj hlgj hrgj
    exact ApplicationBranchProof.atConstructor n H fj.raw domain left right fj.typ fj.gamma fj.pair fj.size fj.label fj.depth
      hc fj.guard hl hr fj.typed fj.bounds fj.paired fj.measured fj.ih
  · exact OriginalTypedDecoderTransportRejectedProof.argumentsOther H 2 (by decide) (by decide)
      f.raw payload f.typ f.gamma f.conclusion hp f.typed

theorem cons (f : Frame n H arguments body alpha Delta) (payload first second : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing f.raw (numeral 7) payload)))
    (hf : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) first f.raw)))
    (hs : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.secondOf (.projection 0)) second f.raw)))
    (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) first)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) second))) :
    Nonempty (Derivation body Delta f.conclusion) := by
  cases arguments
  · exact OriginalTypedDecoderTransportRejectedProof.termSeven H f.raw payload f.typ f.gamma f.conclusion hp f.typed
  · apply OriginalRawSyntaxTransportInternalParserBinaryProof.consCases f.raw f.conclusion
      (pairLeft f.raw (numeral 7) payload hp)
    intro beta j Theta domain left right hj hc
    rw [conclusionRename f j Theta hj]
    let fj := f.rename j Theta hj
    have hfj := renameInto hf j Theta hj
    have hsj := renameInto hs j Theta hj
    have hlgj := renameInto hlg j Theta hj
    have hrgj := renameInto hrg j Theta hj
    simp only [graph1Rename,sucRelabel,zRelabel] at hfj hsj hlgj hrgj
    obtain ⟨hl,hr⟩ := SelectorGuardProof.cons n fj.raw domain left right (first.relabel j) (second.relabel j)
      hc hfj hsj hlgj hrgj
    exact ConsBranchProof.atConstructor n H fj.raw domain left right fj.typ fj.gamma fj.pair fj.size fj.label fj.depth
      hc fj.guard hl hr fj.typed fj.bounds fj.paired fj.measured fj.ih

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.BinaryDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.BinaryDispatchProof
