module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTagEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTagSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTagProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalRepresentativeTag InternalRepresentativeTagSupportProof
open InternalApplicationCertificateConstructorsProof

theorem actualOriginalRepresentativeOuterType :
    InternalRepresentativeTagTargets.ActualOriginalRepresentativeOuterType :=
  InternalRepresentativeTagEvaluationProof.actualOriginalRepresentativeOuterType

theorem actualOriginalRepresentativeWrapperCalibration :
    InternalRepresentativeTagTargets.ActualOriginalRepresentativeWrapperCalibration :=
  InternalRepresentativeTagEvaluationProof.actualOriginalRepresentativeWrapperCalibration

theorem actualOriginalRepresentativeTagsEqual :
    InternalRepresentativeTagTargets.ActualOriginalRepresentativeTagsEqual := by
  intro body valid oldRepresentative α rawTag outTag out raw
  obtain ⟨h⟩ := tagsEqual (body := body) (Gamma := [_,_])
    valid oldRepresentative rawTag outTag out raw
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction h)⟩

theorem actualOriginalRepresentativeTagTransport :
    InternalRepresentativeTagTargets.ActualOriginalRepresentativeTagTransport := by
  intro body valid oldRepresentative α tag out raw
  apply guardedIff
  · exact tagBackward valid oldRepresentative tag out raw
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact tagForward valid oldRepresentative tag out raw
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTagProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTagProof
