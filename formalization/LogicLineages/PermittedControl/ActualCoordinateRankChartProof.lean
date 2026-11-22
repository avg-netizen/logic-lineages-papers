module
public import LogicLineages.PermittedControl.ActualCoordinateRankChartTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCoordinateRankChart

private theorem actualCell (θ : Nat → Nat) (names : List Nat) (name : Nat) (h : name ∈ names) :
    θ name ∈ cells θ names := by
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨name,h,rfl⟩)

private theorem rankRecovers (θ : Nat → Nat) (names : List Nat) (name : Nat) (h : name ∈ names) :
    rankOf θ names name < size θ names ∧ rankValue θ names (rankOf θ names name) = θ name := by
  let value : cells θ names := ⟨θ name,actualCell θ names name h⟩
  let i := (ordered θ names).symm value
  have rank : rankOf θ names name = i.val := by
    rw [rankOf,dif_pos (actualCell θ names name h)]
  have actual : (ordered θ names i).val = θ name :=
    congrArg Subtype.val ((ordered θ names).apply_symm_apply value)
  rw [rank]
  refine ⟨i.isLt,?_⟩
  rw [rankValue,dif_pos i.isLt]
  exact actual

private theorem rankStrict (θ : Nat → Nat) (names : List Nat) :
    StrictMono (rankValue θ names) := by
  intro i j h
  by_cases hj : j < size θ names
  · have hi : i < size θ names := h.trans hj
    rw [rankValue,dif_pos hi,rankValue,dif_pos hj]
    have orderedLt : ordered θ names ⟨i,hi⟩ < ordered θ names ⟨j,hj⟩ :=
      (ordered θ names).strictMono h
    exact orderedLt
  · by_cases hi : i < size θ names
    · rw [rankValue,dif_pos hi,rankValue,dif_neg hj]
      let x : cells θ names := ordered θ names ⟨i,hi⟩
      have le : x.val ≤ (cells θ names).sup id := Finset.le_sup (f := id) x.property
      change x.val < (cells θ names).sup id + j + 1
      omega
    · rw [rankValue,dif_neg hi,rankValue,dif_neg hj]
      omega

private theorem rankEvery (θ : Nat → Nat) (names : List Nat) (k : Nat) (h : k < size θ names) :
    ∃ name ∈ names, rankOf θ names name = k := by
  let x : cells θ names := ordered θ names ⟨k,h⟩
  obtain ⟨name,member,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp x.property)
  have recovers := (rankRecovers θ names name member).2
  have actual : rankValue θ names k = x.val := by rw [rankValue,dif_pos h]
  exact ⟨name,member,(rankStrict θ names).injective (recovers.trans (eq.trans actual.symm))⟩

theorem exactDenseRankChart : ExactDenseRankChart := by
  intro θ names
  have strict := rankStrict θ names
  refine ⟨strict,rankRecovers θ names,rankEvery θ names,?_⟩
  intro i hi j hj
  have left := (rankRecovers θ names i hi).2
  have right := (rankRecovers θ names j hj).2
  constructor
  · constructor
    · intro eq
      exact left.symm.trans ((congrArg (rankValue θ names) eq).trans right)
    · intro eq
      exact strict.injective (left.trans (eq.trans right.symm))
  · constructor
    · intro lt
      have orderedLt := strict lt
      rw [left,right] at orderedLt
      exact orderedLt
    · intro lt
      apply strict.lt_iff_lt.mp
      rw [left,right]
      exact lt

end LogicLineages.PermittedControl.ActualCoordinateRankChart
