module
public import LogicLineages.OrdinalComparison.OneInputBooleanTailProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.OneInputBoolean

theorem point_membership (N x : Nat) : x∈((List.range (N+1)).drop 1) ↔ 0<x ∧ x≤N := by
  rw [List.range_eq_range',List.drop_range']
  simp only [Nat.zero_add,Nat.one_mul,Nat.add_sub_cancel,List.mem_range'_1]
  omega

theorem closures_correct (formula : OneInputBooleanExpr) (hv : oneInputBooleanValid formula) :
    ((encodedOneInputBooleanClosures (oneInputBooleanCompile formula)).1=true ↔
      ∃ x : Nat,0<x ∧ actualOneInputBooleanValue formula x=true) ∧
    ((encodedOneInputBooleanClosures (oneInputBooleanCompile formula)).2=true ↔
      ∀ x : Nat,0<x → actualOneInputBooleanValue formula x=true) := by
  let program := oneInputBooleanCompile formula
  let N := encodedOneInputBooleanTail program
  have hN : 0<N := (source_tail formula hv).1
  have hTail : ∀ x : Nat,N≤x → actualOneInputBooleanValue formula x=actualOneInputBooleanValue formula N :=
    (source_tail formula hv).2
  have hNmem : N∈((List.range (N+1)).drop 1) := (point_membership N N).mpr ⟨hN,le_rfl⟩
  constructor
  · change ((List.range (N+1)).drop 1).any (encodedOneInputBooleanValue program)=true ↔ _
    rw [List.any_eq_true]
    constructor
    · rintro ⟨x,hm,hx⟩
      exact ⟨x,((point_membership N x).mp hm).1,(source_value formula hv x) ▸ hx⟩
    · rintro ⟨x,hx,hTrue⟩
      by_cases hle : x≤N
      · refine ⟨x,(point_membership N x).mpr ⟨hx,hle⟩,?_⟩
        rw [source_value formula hv x]
        exact hTrue
      · refine ⟨N,hNmem,?_⟩
        rw [source_value formula hv N,←hTail x (by omega)]
        exact hTrue
  · change ((List.range (N+1)).drop 1).all (encodedOneInputBooleanValue program)=true ↔ _
    rw [List.all_eq_true]
    constructor
    · intro h x hx
      by_cases hle : x≤N
      · have hm := h x ((point_membership N x).mpr ⟨hx,hle⟩)
        rw [source_value formula hv x] at hm
        exact hm
      · have hm := h N hNmem
        rw [source_value formula hv N] at hm
        rw [hTail x (by omega)]
        exact hm
    · intro h x hm
      rw [source_value formula hv x]
      exact h x ((point_membership N x).mp hm).1

theorem full : Targets.FullActualOneInputBooleanClosures := ⟨programs,source_value,source_tail,closures_correct⟩

end LogicLineages.OrdinalComparison.OneInputBoolean
