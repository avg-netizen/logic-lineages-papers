module
public import LogicLineages.StandardControlCurrent.HyperCloseBlockTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindowProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindowCodeProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.HyperCloseBlockProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion HyperCloseBlock

private def E : List Nat → ((Nat → Nat) → Prop) → (Nat → Nat) → Prop
  | [],P,ν => P ν
  | x::xs,P,ν => ∃ n : Nat, E xs P (Function.update ν x n)

private theorem e_names (xs : List Nat) (p : Matrix) (ν : Nat → Nat) :
    E xs p.eval ν ↔ existsNames xs p ν := by
  induction xs generalizing ν with
  | nil => rfl
  | cons x xs ih => simp only [E,existsNames,ih]

private theorem e_projection (xs : List Nat) (P : (Nat → Nat) → Prop) (ν : Nat → Nat) :
    E xs P ν ↔ ∃ ρ : Nat → Nat, (∀ i, i ∉ xs → ρ i=ν i) ∧ P ρ := by
  induction xs generalizing ν with
  | nil =>
    constructor
    · intro h; exact ⟨ν,fun _ _ => rfl,h⟩
    · rintro ⟨ρ,he,hp⟩
      have hρ : ρ=ν := funext (fun i => he i (by simp))
      simpa [hρ,E] using hp
  | cons x xs ih =>
    simp only [E,ih]
    constructor
    · rintro ⟨n,ρ,he,hp⟩
      refine ⟨ρ,?_,hp⟩
      intro i hi
      have hn : i ∉ xs := by intro h; exact hi (List.mem_cons_of_mem x h)
      have hx : i ≠ x := by intro h; subst i; exact hi (by simp)
      rw [he i hn]
      simp [Function.update,hx]
    · rintro ⟨ρ,he,hp⟩
      refine ⟨ρ x,ρ,?_,hp⟩
      intro i hi
      by_cases hx : i=x
      · subst i; simp
      · rw [he i (by simp [hx,hi])]
        simp [Function.update,hx]

private theorem e_set (xs ys : List Nat) (P : (Nat → Nat) → Prop) (ν : Nat → Nat)
    (he : ∀ i, i ∈ xs ↔ i ∈ ys) : E xs P ν ↔ E ys P ν := by
  simp only [e_projection,he]

private theorem e_append (xs ys : List Nat) (P : (Nat → Nat) → Prop) (ν : Nat → Nat) :
    E (xs++ys) P ν ↔ E xs (fun ρ => E ys P ρ) ν := by
  induction xs generalizing ν with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append,E,ih]

private theorem e_congr (xs : List Nat) (P Q : (Nat → Nat) → Prop)
    (he : ∀ ν, P ν ↔ Q ν) (ν : Nat → Nat) : E xs P ν ↔ E xs Q ν := by
  simp only [e_projection,he]

private theorem e_or (xs : List Nat) (P Q : (Nat → Nat) → Prop) (ν : Nat → Nat) :
    E xs (fun ρ => P ρ ∨ Q ρ) ν ↔ E xs P ν ∨ E xs Q ν := by
  simp only [e_projection]
  constructor
  · rintro ⟨ρ,ha,hp|hq⟩
    · exact Or.inl ⟨ρ,ha,hp⟩
    · exact Or.inr ⟨ρ,ha,hq⟩
  · rintro (⟨ρ,ha,hp⟩|⟨ρ,ha,hq⟩)
    · exact ⟨ρ,ha,Or.inl hp⟩
    · exact ⟨ρ,ha,Or.inr hq⟩

theorem actualAlternatives : HyperCloseBlockTargets.ActualAlternatives :=
  HyperWindowProof.actualCollisionAlternatives

theorem pairElimination : HyperCloseBlockTargets.PairElimination := by
  intro i j hij e h k l c p ν
  exact HyperWindowProof.actualTwoVariableElimination i j hij e h k l c p ν

theorem blockPermutation : HyperCloseBlockTargets.BlockPermutation := by
  intro xs ys p ν hn hp
  rw [← e_names,← e_names]
  exact e_set xs ys p.eval ν (fun i => hp.mem_iff)

theorem blockElimination : HyperCloseBlockTargets.BlockElimination := by
  intro xs i j e h k l c p ν hn hi hj hij
  let rest := (xs.erase i).erase j
  have hr (z : Nat) : z ∈ rest ↔ z ≠ j ∧ z ≠ i ∧ z ∈ xs := by
    simp only [rest,(List.Nodup.erase i hn).mem_erase_iff,hn.mem_erase_iff]
  have hfull (z : Nat) : z ∈ xs ↔ z ∈ rest++[i,j] := by
    simp only [List.mem_append,List.mem_cons,List.mem_singleton,hr]
    constructor
    · intro hz
      by_cases hzi : z=i
      · exact Or.inr (Or.inl hzi)
      · by_cases hzj : z=j
        · exact Or.inr (Or.inr hzj)
        · exact Or.inl ⟨hzj,hzi,hz⟩
    · rintro (⟨_,_,hz⟩ | hz | hz) <;> subst_vars <;> assumption
  have hleft (z : Nat) : z ∈ xs.erase i ↔ z ∈ rest++[j] := by
    simp only [hn.mem_erase_iff,List.mem_append,List.mem_singleton,hr]
    constructor
    · rintro ⟨hzi,hz⟩
      by_cases hzj : z=j
      · exact Or.inr hzj
      · exact Or.inl ⟨hzj,hzi,hz⟩
    · rintro (⟨hzj,hzi,hz⟩|rfl)
      · exact ⟨hzi,hz⟩
      · exact ⟨hij.symm,hj⟩
  have hright (z : Nat) : z ∈ xs.erase j ↔ z ∈ rest++[i] := by
    simp only [hn.mem_erase_iff,List.mem_append,List.mem_singleton,hr]
    constructor
    · rintro ⟨hzj,hz⟩
      by_cases hzi : z=i
      · exact Or.inr hzi
      · exact Or.inl ⟨hzj,hzi,hz⟩
    · rintro (⟨hzj,hzi,hz⟩|rfl)
      · exact ⟨hzj,hz⟩
      · exact ⟨hij,hi⟩
  have rearrange (ys : List Nat) (q : Matrix) (zs : List Nat)
      (he : ∀ z, z ∈ ys ↔ z ∈ rest++zs) :
      existsNames ys q ν ↔ E rest (fun ρ => E zs q.eval ρ) ν := by
    rw [← e_names]
    exact (e_set ys (rest++zs) q.eval ν he).trans (e_append rest zs q.eval ν)
  rw [rearrange xs (.conjunction (HyperWindow.closeMatrix i j e h k l c) p) [i,j] hfull]
  have hp := e_congr rest _ _ (pairElimination i j hij e h k l c p) ν
  simp only [E] at hp
  rw [hp,e_or,e_or]
  simp only [result,branches,List.mem_cons,List.not_mem_nil,or_false]
  rw [← rearrange (xs.erase i) (HyperWindow.leftCases i j e h k l c p) [j] hleft,
    ← rearrange (xs.erase j) (HyperWindow.rightCases i j e h k l c p) [i] hright,
    ← rearrange (xs.erase i) (HyperWindow.equalCases i j e h k l c p) [j] hleft]
  simp

theorem strictDecrease : HyperCloseBlockTargets.StrictDecrease := by
  intro xs i j e h k l c p hn hi hj hij b hb
  have hs := HyperWindowProof.exactSupportReduction i j hij e h k l c p
  have base (a : Nat) (ha : a ∈ xs) (q : Matrix)
      (hq : ∀ z, z ∈ q.variables → z ≠ a ∧ (z ∈ xs ∨ z ∈ p.variables)) :
      (xs.erase a).Nodup ∧ (xs.erase a).length+1=xs.length ∧ (xs.erase a).length<xs.length ∧
      ∀ z, z ∈ q.variables → z ∉ xs.erase a → z ∈ p.variables ∧ z ∉ xs := by
    have hl := List.length_erase_add_one ha
    refine ⟨List.Nodup.erase a hn,hl,by omega,?_⟩
    intro z hz ho
    have h := hq z hz
    have hnxs : z ∉ xs := by
      intro hm
      exact ho (hn.mem_erase_iff.mpr ⟨h.1,hm⟩)
    exact ⟨h.2.resolve_left hnxs,hnxs⟩
  simp only [branches,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl
  · apply base i hi
    intro z hz
    have h := (hs z).1 hz
    exact ⟨h.1,h.2.imp (fun he => he ▸ hj) id⟩
  · apply base j hj
    intro z hz
    have h := (hs z).2.1 hz
    exact ⟨h.1,h.2.imp (fun he => he ▸ hi) id⟩
  · apply base i hi
    intro z hz
    have h := (hs z).2.2 hz
    exact ⟨h.1,h.2.imp (fun he => he ▸ hj) id⟩

theorem literalCode : HyperCloseBlockTargets.LiteralCode := by
  intro xs i j e h k l c p
  obtain ⟨hl,hr,he⟩ := HyperWindowCodeProof.literalCalibration i j e h k l c p
  simp only [program,branches,List.map_cons,List.map_nil,hl,hr,he]
  rfl
end LogicLineages.StandardControlCurrent.HyperCloseBlockProof
