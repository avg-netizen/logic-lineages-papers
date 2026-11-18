module
public import LogicLineages.PermittedControl.HighestPhaseGeometryTargets
public import LogicLineages.PermittedControl.HighestPieceProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem profile_list_max_properties (l : List Ordinal.{0}) :
    (l.foldr max 0=0 ∨ l.foldr max 0 ∈ l) ∧ ∀ b ∈ l, b ≤ l.foldr max 0 := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldr_cons]
    constructor
    · by_cases hb : b ≤ l.foldr max 0
      · rw [max_eq_right hb]
        rcases ih.1 with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rw [max_eq_left (le_of_not_ge hb)]
        exact Or.inr List.mem_cons_self
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_max_left _ _
      · exact (ih.2 x hx).trans (le_max_right _ _)

 theorem profile_list_max_lt (l : List Ordinal.{0}) (z : Ordinal.{0}) (hz : 0 < z)
    (hl : ∀ b ∈ l, b < z) : l.foldr max 0 < z := by
  induction l with
  | nil => exact hz
  | cons b l ih =>
    exact max_lt (hl b List.mem_cons_self) (ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)))

 theorem profile_list_min_properties (l : List Ordinal.{0}) (E : Ordinal.{0}) :
    (l.foldr min E=E ∨ l.foldr min E ∈ l) ∧ l.foldr min E ≤ E ∧ ∀ b ∈ l, l.foldr min E ≤ b := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldr_cons]
    refine ⟨?_,(min_le_right _ _).trans ih.2.1,?_⟩
    · by_cases hb : b ≤ l.foldr min E
      · rw [min_eq_left hb]
        exact Or.inr List.mem_cons_self
      · rw [min_eq_right (le_of_not_ge hb)]
        rcases ih.1 with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (ih.2.2 x hx)

 theorem profile_list_min_lower (l : List Ordinal.{0}) (E z : Ordinal.{0}) (hz : z ≤ E)
    (hl : ∀ b ∈ l, z ≤ b) : z ≤ l.foldr min E := by
  induction l with
  | nil => exact hz
  | cons b l ih =>
    exact le_min (hl b List.mem_cons_self) (ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)))

 theorem joint_breakpoint_norm_bound (mu nu b : Ordinal.{0}) (hmu : mu < epsilonZero) (hnu : nu < epsilonZero)
    (hb : b ∈ jointProfileBreakpoints mu nu) :
    b < epsilonZero ∧ actualOrdinalNorm b ≤ actualOrdinalNorm mu+actualOrdinalNorm nu := by
  rcases List.mem_append.mp hb with hb | hb
  · have hh := actual_profile_breakpoint_bound mu hmu b hb
    exact ⟨hh.1,hh.2.trans (Nat.le_add_right _ _)⟩
  · have hh := actual_profile_breakpoint_bound nu hnu b hb
    exact ⟨hh.1,hh.2.trans (Nat.le_add_left _ _)⟩

/-- Actual finite breakpoint boundaries; zero is only the harmless lower
sentinel, and E the upper clipping sentinel. -/
 theorem profile_piece_boundaries (mu nu E z : Ordinal.{0}) (hz : 0 < z) (hzE : z < E) :
    ∃ a U : Ordinal.{0}, a < z ∧ z ≤ U ∧ U ≤ E ∧
      (a=0 ∨ a ∈ jointProfileBreakpoints mu nu) ∧
      (U=E ∨ U ∈ jointProfileBreakpoints mu nu) ∧
      (∀ y : Ordinal.{0}, a < y → y ≤ U → SameProfilePiece mu nu y z) := by
  classical
  let lo := (jointProfileBreakpoints mu nu).filter (fun b => b < z)
  let hi := (jointProfileBreakpoints mu nu).filter (fun b => z ≤ b)
  let a := lo.foldr max 0
  let U := hi.foldr min E
  have hal := profile_list_max_properties lo
  have hul := profile_list_min_properties hi E
  have haz : a < z := profile_list_max_lt lo z hz (fun b hb => of_decide_eq_true (List.mem_filter.mp hb).2)
  have hzU : z ≤ U := profile_list_min_lower hi E z hzE.le (fun b hb => of_decide_eq_true (List.mem_filter.mp hb).2)
  refine ⟨a,U,haz,hzU,hul.2.1,?_,?_,?_⟩
  · rcases hal.1 with ha | ha
    · exact Or.inl ha
    · exact Or.inr (List.mem_filter.mp ha).1
  · rcases hul.1 with hU | hU
    · exact Or.inl hU
    · exact Or.inr (List.mem_filter.mp hU).1
  · intro y hay hyU b hb
    by_cases hzb : z ≤ b
    · have hbhi : b ∈ hi := List.mem_filter.mpr ⟨hb,by simpa using hzb⟩
      have hyb : y ≤ b := hyU.trans (hul.2.2 b hbhi)
      exact ⟨fun _ => hzb,fun _ => hyb⟩
    · have hbl : b ∈ lo := List.mem_filter.mpr ⟨hb,by simpa using lt_of_not_ge hzb⟩
      have hby : b < y := (hal.2 b hbl).trans_lt hay
      exact ⟨fun hyb => False.elim ((not_le_of_gt hby) hyb),fun hzbad => False.elim (hzb hzbad)⟩

end LogicLineages.PermittedControl
