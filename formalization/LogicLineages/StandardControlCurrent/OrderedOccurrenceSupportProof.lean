module
public import LogicLineages.StandardControlCurrent.OrderedOccurrenceProvenanceProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormSemanticProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.OrderedOccurrenceProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion OrderedOccurrence

private theorem all_variables (ps : List Matrix) (i : Nat) :
    i ∈ (OrderedOccurrence.all ps).variables ↔ ∃ p∈ps, i∈p.variables := by
  induction ps with
  | nil => simp [OrderedOccurrence.all,Matrix.variables]
  | cons p ps ih => simp [OrderedOccurrence.all,Matrix.variables,ih]

private theorem summand_variables (s : NormalForm.Summand) : s.term.variables=[s.name] := by
  cases s <;> simp [NormalForm.Summand.term,NormalForm.Summand.name,
    HyperWindow.valueTerm,HyperWindow.innerTerm,HyperWindow.indexTerm,shiftTerm,Term.variables]

private theorem strict_variables (xs : List Nat) (z : Nat)
    (hz : z∈(strictOrder xs).variables) : z∈xs := by
  obtain ⟨q,hq,hz⟩ := (all_variables _ z).mp hz
  obtain ⟨⟨i,k⟩,hi,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  have hi' : i∈xs := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hi)
  have hj' : j∈xs := List.mem_of_mem_drop hj
  have he : z=j ∨ z=i := by simpa [Matrix.variables,Term.variables] using hz
  rcases he with rfl | rfl
  · exact hj'
  · exact hi'

private theorem maximal_variables (xs : List Nat) (p : NormalForm.Formula)
    (o : Occurrence) (ho : o∈live xs p) (z : Nat)
    (hz : z∈(maximal xs p o).variables) : z∈xs := by
  obtain ⟨q,hq,hz⟩ := (all_variables _ z).mp hz
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
  have ha' := (exactLive xs p a).mp ha
  have ho' := (exactLive xs p o).mp ho
  have he : z=(summand a).name ∨ z=(summand o).name := by
    simpa [atMost,Matrix.variables,summand_variables,or_comm] using hz
  rcases he with rfl | rfl
  · exact ha'.2.2.2
  · exact ho'.2.2.2

theorem freeSupport : OrderedOccurrenceTargets.FreeSupport := by
  intro xs p o hn ho z hz hzb
  by_cases hx : xs=[]
  · subst xs
    simp only [dispatch,↓reduceIte,List.mem_singleton] at ho
    subst o
    exact ⟨(NormalFormSemanticProof.exactVariableMembership p z).mp hz,by simp⟩
  by_cases hi : inactive xs p=[]
  · simp only [dispatch,if_neg hx,if_pos hi,List.mem_append] at ho
    rcases ho with ht | ht
    · obtain ⟨i,hi',ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ht
      have hj' : j∈xs ∧ j≠i := by simpa using hj
      have hs := (WindowProof.matrix_support p.compile (.variable j) i z).mp hz
      rcases hs with ⟨hp,hzi⟩ | ⟨_,hjz⟩
      · refine ⟨(NormalFormSemanticProof.exactVariableMembership p z).mp hp,?_⟩
        intro hzx
        exact hzb (hn.mem_erase_iff.mpr ⟨hzi,hzx⟩)
      · have he : z=j := by simpa [Term.variables] using hjz
        subst z
        exact False.elim (hzb (hn.mem_erase_iff.mpr ⟨hj'.2,hj'.1⟩))
    · obtain ⟨ys,hy,ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨⟨a,k⟩,ha,rfl⟩ := List.mem_map.mp ht
      have hp : ys.Perm xs := List.mem_permutations.mp hy
      have hzxs : z∉xs := fun h => hzb (hp.mem_iff.mpr h)
      have ham : a∈live xs p := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp ha)
      simp only [Matrix.variables,List.mem_append] at hz
      rcases hz with hz | hz | hz
      · exact False.elim (hzb (strict_variables ys z hz))
      · exact False.elim (hzxs (maximal_variables xs p a ham z hz))
      · exact ⟨(NormalFormSemanticProof.exactVariableMembership p z).mp hz,hzxs⟩
  · simp only [dispatch,if_neg hx,if_neg hi] at ho
    obtain ⟨i,hi',rfl⟩ := List.mem_map.mp ho
    exact ⟨(NormalFormSemanticProof.exactVariableMembership p z).mp hz,hzb⟩
end LogicLineages.StandardControlCurrent.OrderedOccurrenceProof
