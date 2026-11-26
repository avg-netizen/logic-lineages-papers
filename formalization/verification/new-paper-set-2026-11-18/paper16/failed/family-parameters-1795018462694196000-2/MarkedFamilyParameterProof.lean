import LogicLineages.PersistentMarking.MarkedFamilyParameterTargets
import LogicLineages.PersistentMarking.MarkedBaseTupleFoundationProof
import LogicLineages.PersistentMarking.MarkedBaseHeadCoverageProof
import LogicLineages.PersistentMarking.MarkedExtrasEnumerationProof
namespace LogicLineages.PersistentMarking.MarkedFamilyParameterProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics MarkedFamilyParameters

theorem parameterEqExact (a b : Parameter) : parameterEq a b = true ↔ a=b := by
  rcases a with ⟨f,τ,Γ,bs,es⟩
  rcases b with ⟨g,υ,Θ,cs,fs⟩
  simp only [parameterEq,Bool.and_eq_true,decide_eq_true_eq,Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨⟨hf,ht⟩,hg⟩,hb⟩,he⟩
    exact ⟨hf,ht,hg,hb,he⟩
  · rintro ⟨hf,ht,hg,hb,he⟩
    exact ⟨⟨⟨⟨hf,ht⟩,hg⟩,hb⟩,he⟩

theorem enumeration : MarkedFamilyParameterTargets.Enumeration := by
  intro E heads p
  unfold parameters
  rw [FiniteEqualityProof.dedupMem _ parameterEqExact]
  constructor
  · intro h
    obtain ⟨f,hf,h⟩ := List.mem_flatMap.mp h
    obtain ⟨τ,ht,h⟩ := List.mem_flatMap.mp h
    obtain ⟨Γ,hg,h⟩ := List.mem_flatMap.mp h
    obtain ⟨bs,hb,h⟩ := List.mem_flatMap.mp h
    obtain ⟨es,he,hp⟩ := List.mem_map.mp h
    cases hp
    exact ⟨hf,ht,(DecisionPortsProof.enumeration _ _ _).mp hg,
      (MarkedBaseTupleFoundationProof.enumeration E Γ f.arguments bs).mp hb,
      (MarkedExtrasEnumerationProof.enumeration E Γ es).mp he⟩
  · rcases p with ⟨f,τ,Γ,bs,es⟩
    rintro ⟨hf,ht,hg,hb,he⟩
    exact List.mem_flatMap.mpr ⟨f,hf,List.mem_flatMap.mpr ⟨τ,ht,
      List.mem_flatMap.mpr ⟨Γ,(DecisionPortsProof.enumeration _ _ _).mpr hg,
      List.mem_flatMap.mpr ⟨bs,(MarkedBaseTupleFoundationProof.enumeration E Γ f.arguments bs).mpr hb,
      List.mem_map.mpr ⟨es,(MarkedExtrasEnumerationProof.enumeration E Γ es).mpr he,rfl⟩⟩⟩⟩⟩

theorem distinct : MarkedFamilyParameterTargets.Distinct := by
  intro E heads
  exact FiniteEqualityProof.dedupDistinct _ parameterEqExact _

theorem schemaExact : MarkedFamilyParameterTargets.SchemaExact := by
  intro E heads p n
  constructor
  · intro h
    obtain ⟨q,hq,h⟩ := List.mem_map.mp h
    cases h
    exact ⟨(enumeration E heads q).mp hq,rfl⟩
  · rintro ⟨hp,rfl⟩
    exact List.mem_map.mpr ⟨p,(enumeration E heads p).mpr hp,rfl⟩

theorem schemaDistinct : MarkedFamilyParameterTargets.SchemaDistinct := by
  intro E heads
  have he : (MarkedFamilyParameters.schema E heads).map Prod.fst = parameters E heads := by
    change ((parameters E heads).map (fun p => (p,bound E p))).map Prod.fst = _
    rw [List.map_map]
    exact List.map_id (parameters E heads)
  rw [he]
  exact distinct E heads

theorem sourceCoverage : MarkedFamilyParameterTargets.SourceCoverage := MarkedBaseHeadCoverageProof.coverage
end LogicLineages.PersistentMarking.MarkedFamilyParameterProof
