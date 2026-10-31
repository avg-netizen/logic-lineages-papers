module

public import LogicLineages.ComputabilityKnowledge.GorbowSourceRegistryPaddingTargets
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
public import LogicLineages.ComputabilityKnowledge.GorbowDiagonalRegistryProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedRegistryProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSourceRegistryPadding.Proof
open GorbowPRProgram GorbowPRRegistry List.Vector

theorem layout : Targets.Layout := by
  intro pF pR
  simp [root, arguments, wrapper, nodes, paddingPrefix, middle, dummy,
    List.ofFn_succ, List.append_assoc]

private theorem subtreeRoot {n : Nat} (p : Program n) (before after : List Packed) :
    (before ++ nodes p ++ after)[before.length]? = some ⟨n,p⟩ := by
  rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self]
  cases p <;> rfl

theorem functionRoot : Targets.FunctionRoot := by
  intro pF pR
  rw [layout]
  cases pF <;> rfl

theorem relationRoot : Targets.RelationRoot := by
  intro pF pR
  rw [layout]
  have hlen : (paddingPrefix pF pR ++ nodes pF ++ middle pR).length = relationTag pF := by
    simp [paddingPrefix, middle, relationTag]
    omega
  have h := subtreeRoot pR (paddingPrefix pF pR ++ nodes pF ++ middle pR) [⟨4,dummy⟩]
  rw [hlen] at h
  exact h

theorem lowTagsHighArity : Targets.LowTagsHighArity := by
  intro pF pR tag a htag ht
  rw [layout] at ht
  simp only [List.append_assoc] at ht
  have hbound : tag < (paddingPrefix pF pR).length := by
    simp only [paddingPrefix, List.length_cons, List.length_nil]
    omega
  rw [List.getElem?_append_left hbound] at ht
  have hm : a ∈ paddingPrefix pF pR := List.mem_iff_getElem?.mpr ⟨tag,ht⟩
  simp only [paddingPrefix, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp <;> decide

private theorem nameBounds (name : Nat × Nat) (h : name ∈ functionNames) :
    name.1 ≤ 3 ∧ name.2 ≤ 4 := by
  simp only [functionNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem headerDisjoint : Targets.HeaderDisjoint := by
  intro pF pR tag a ht name hn he
  subst name
  obtain ⟨ha,hb⟩ := nameBounds (a.1,tag) hn
  have hlarge := lowTagsHighArity pF pR tag a hb ht
  omega

theorem specificPrograms : Targets.SpecificPrograms := by
  have hF : Primrec sourceFunction := GorbowDiagonalRegistryProof.uniformProgram
  have hR : Primrec sourceRelationValue := by
    have h := Primrec.cond GorbowSortedRegistryProof.uniformPrograms.1
      (Primrec.const (1 : Nat)) (Primrec.const 0)
    exact h.of_eq (fun code => by
      cases hcode : GorbowSortedRegistry.relationProgram code <;>
        simp [sourceRelationValue, hcode])
  obtain ⟨pF,hpF⟩ := (GorbowPRProgram.Proof.unaryCorrespondence sourceFunction).mp hF
  obtain ⟨pR,hpR⟩ := (GorbowPRProgram.Proof.unaryCorrespondence sourceRelationValue).mp hR
  exact ⟨hF,hR,pF,pR,hpF,hpR⟩

end LogicLineages.ComputabilityKnowledge.GorbowSourceRegistryPadding.Proof
