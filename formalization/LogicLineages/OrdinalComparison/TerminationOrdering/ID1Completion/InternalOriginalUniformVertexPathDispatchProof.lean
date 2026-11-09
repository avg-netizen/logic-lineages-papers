module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathDispatchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformVertexPath InternalOriginalUniformVertexPathTargets
open InternalOriginalUniformVertexPathSupportProof InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualParameterizedVertexActivation : ActualParameterizedVertexActivation := by
  intro body data α Delta p d e a x arrow
  let h := graph2 InternalListCodec.consCode arrow d e
  let g := activationAccepted data p d e a x
  let f := activationFactors data p d a x arrow
  obtain ⟨hf⟩ := activationRecover (body := body) (Gamma := g :: h :: Delta)
    data p d e a x arrow
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := activationAccept (body := body) (Gamma := f :: h :: Delta)
    data p d e a x arrow
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

theorem actualParameterizedVertexDispatch : ActualParameterizedVertexDispatch := by
  intro body data oldVertex α Delta out p d e a x
  constructor
  · let h := activationAccepted data p d e a x
    let g := vertexGraph data oldVertex out p d e a x
    let f := InternalParameterizedCanonicalResultFold.applicationGraph data out d e x a p
    obtain ⟨hf⟩ := vertexRecover (body := body) (Gamma := g :: h :: Delta)
      data oldVertex p d e a x out
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hb⟩ := vertexAccept (body := body) (Gamma := f :: h :: Delta)
      data oldVertex p d e a x out
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
      (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩
  · let h := activationGraph data OrdinaryArithmetic.zeroTerm p d e a x
    let g := vertexGraph data oldVertex out p d e a x
    let f := oldVertexGraph oldVertex out p d e a x
    obtain ⟨hf⟩ := inactiveRecover (body := body) (Gamma := g :: h :: Delta)
      data oldVertex p d e a x out
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hb⟩ := inactiveAccept (body := body) (Gamma := f :: h :: Delta)
      data oldVertex p d e a x out
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
      (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

theorem actualParameterizedVertexInvariantFactors : ActualParameterizedVertexInvariantFactors := by
  intro body data α Delta p d e a x arrow
  let h := graph2 InternalListCodec.consCode arrow d e
  let g := invariantAccepted data p d e a x
  let f := invariantFactors data p d e a x arrow
  obtain ⟨hf⟩ := invariantRecover (body := body) (Gamma := g :: h :: Delta)
    data p d e a x arrow
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := invariantAccept (body := body) (Gamma := f :: h :: Delta)
    data p d e a x arrow
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathDispatchProof
