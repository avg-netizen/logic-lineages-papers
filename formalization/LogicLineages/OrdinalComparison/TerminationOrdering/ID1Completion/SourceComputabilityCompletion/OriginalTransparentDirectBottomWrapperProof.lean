module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomWrapperSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomSourceSpineProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomWrapperProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalTransparentDirectBottom
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Concrete decoder acceptance pays the spine condition. The remaining
wrapper and hereditary nil-path guards are constructed, never assumed. -/
theorem actualOriginalConcreteDirectBottomClosedLeaf :
    OriginalTransparentDirectBottomTargets.ActualOriginalConcreteDirectBottomClosedLeaf := by
  intro H G M W oldStep endpoint window body alpha Delta s t cert parameter typ
  let source := OriginalUniverseDecoder.source H G M W
  let A := Premises source s t cert parameter typ
  have h : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hs := andLeft h
  have hn := andLeft (andRight h)
  have hb := andLeft (andRight (andRight (andRight h)))
  have hspine := OriginalTransparentDirectBottomSourceSpineProof.sourceSpine
    H G M W s t cert parameter typ hs hn hb
  obtain ⟨hout⟩ := OriginalTransparentDirectBottomWrapperSupportProof.closedFromSpine
    source oldStep endpoint window s t cert parameter typ h hspine
  exact ⟨Derivation.implicationIntroduction hout⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomWrapperProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomWrapperProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomWrapperProof.actualOriginalConcreteDirectBottomClosedLeaf
