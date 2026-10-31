module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedRegistryInterpretationTargets
public import LogicLineages.ComputabilityKnowledge.GorbowSourceRegistryPaddingProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRDefiningEquationsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedRegistryInterpretation.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowSourceRegistryPadding List.Vector

theorem internalHeader : Targets.InternalHeader := by
  intro pF pR tag m q args h ht
  have hd := (GorbowRegistryDecoderProof.headerExact
    (GorbowRegistryTuple.header m tag args) m tag args).mpr rfl
  have hn : (m,tag) ∉ functionNames := by
    intro hname
    exact GorbowSourceRegistryPadding.Proof.headerDisjoint pF pR tag ⟨m,q⟩ ht
      (m,tag) hname rfl
  simpa only [functionProgram, hd, hn, false_and, ite_false] using
    GorbowPRDefiningEquations.Proof.headerCalibration 4 (root pF pR) tag m q args h ht

theorem internalTerm : Targets.InternalTerm := by
  intro ctx pF pR tag m q args I rho ht
  let J := interpretation pF pR I
  have hh := (GorbowRegistryTupleProof.termCalibration ctx J rho).2.2 m tag args.toList
  have hlen : (args.toList.map fun t => t.realize J rho).length = m := by simp
  have hc := internalHeader pF pR tag m q
    (args.toList.map fun t => t.realize J rho) hlen ht
  exact (congrArg (functionProgram pF pR) hh).trans hc

theorem namedFunction : Targets.NamedFunction := by
  intro pF pR name hn args hlen
  obtain ⟨arity,tag⟩ := name
  have hd := (GorbowRegistryDecoderProof.headerExact
    (GorbowRegistryTuple.header arity tag args) arity tag args).mpr rfl
  have hc := GorbowPRRegistry.Proof.exactDispatch 4 (root pF pR) functionTag 1 pF
    [GorbowRegistryTuple.header arity tag args] rfl
    (GorbowSourceRegistryPadding.Proof.functionRoot pF pR)
  simp [functionProgram, hd, hn, hlen, hc]
  rfl

theorem namedRelation : Targets.NamedRelation := by
  intro pF pR name hn args hlen
  obtain ⟨arity,tag⟩ := name
  have hd := (GorbowRegistryDecoderProof.headerExact
    (GorbowRegistryTuple.header arity tag args) arity tag args).mpr rfl
  have hc := GorbowPRRegistry.Proof.exactDispatch 4 (root pF pR) (relationTag pF) 1 pR
    [GorbowRegistryTuple.header arity tag args] rfl
    (GorbowSourceRegistryPadding.Proof.relationRoot pF pR)
  simp [relationProgram, hd, hn, hlen, hc]
  rfl

theorem specificNamedBridge : Targets.SpecificNamedBridge := by
  obtain ⟨_,_,pF,pR,hpF,hpR⟩ := GorbowSourceRegistryPadding.Proof.specificPrograms
  refine ⟨pF,pR,?_,?_⟩
  · intro name hn args hlen
    rw [namedFunction pF pR name hn args hlen]
    exact hpF _
  · intro name hn args hlen
    have hi := namedRelation pF pR name hn args hlen
    rw [hpR] at hi
    cases hnew : relationProgram pF pR (GorbowRegistryTuple.header name.1 name.2 args) <;>
      cases hold : GorbowSortedRegistry.relationProgram (GorbowRegistryTuple.header name.1 name.2 args) <;>
      simp_all [sourceRelationValue]

end LogicLineages.ComputabilityKnowledge.GorbowNamedRegistryInterpretation.Proof
