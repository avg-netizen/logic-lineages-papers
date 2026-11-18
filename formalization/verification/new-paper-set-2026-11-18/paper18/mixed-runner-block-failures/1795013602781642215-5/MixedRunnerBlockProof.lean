module
public import LogicLineages.StandardControlCurrent.MixedRunnerBlockTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ReverseWindowProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearWindowProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ActiveHyperProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.MixedRunnerBlockProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion MixedRunnerBlock
open HyperCloseBlock (existsNames)

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


/-- Derived one-name block elimination, preserving every residual update. -/
theorem block_erase (xs : List Nat) (x : Nat) (before after : Matrix)
    (hn : xs.Nodup) (hx : x ∈ xs)
    (step : ∀ ν, (∃ n : Nat, before.eval (Function.update ν x n)) ↔ after.eval ν)
    (ν : Nat → Nat) : existsNames xs before ν ↔ existsNames (xs.erase x) after ν := by
  have hs (z : Nat) : z ∈ xs ↔ z ∈ xs.erase x ++ [x] := by
    simp only [List.mem_append,List.mem_singleton,hn.mem_erase_iff]
    constructor
    · intro hz
      by_cases he : z=x
      · exact Or.inr he
      · exact Or.inl ⟨he,hz⟩
    · rintro (⟨_,hz⟩ | rfl)
      · exact hz
      · exact hx
  rw [← e_names,← e_names]
  rw [e_set xs (xs.erase x ++ [x]) before.eval ν hs,e_append]
  apply e_congr
  intro ρ
  simpa only [E] using step ρ

 theorem reduction_of_step (xs : List Nat) (x : Nat) (before after : Matrix)
    (step : ∀ ν, (∃ n : Nat, before.eval (Function.update ν x n)) ↔ after.eval ν)
    (support : ∀ name, name ∈ after.variables → name ≠ x ∧ name ∈ before.variables) :
    Reduction xs x before after := by
  intro hn hx
  have hl := List.length_erase_add_one hx
  refine ⟨block_erase xs x before after hn hx step,List.Nodup.erase x hn,hl,by omega,?_⟩
  intro name hm hnot
  obtain ⟨hne,hbefore⟩ := support name hm
  refine ⟨hbefore,?_⟩
  intro hmem
  exact hnot (hn.mem_erase_iff.mpr ⟨hne,hmem⟩)

 theorem reverseWitness : MixedRunnerBlockTargets.ReverseWitness := ReverseWindowProof.actualMinusWitness
 theorem reverseElimination : MixedRunnerBlockTargets.ReverseElimination := by
  intro i anchor e c p hi ν
  exact ReverseWindowProof.actualFiniteElimination i anchor e c p hi ν
 theorem linearBounds : MixedRunnerBlockTargets.LinearBounds :=
  ⟨LinearWindowProof.actualNonlinearLinearBound,LinearWindowProof.actualGuardBound⟩
 theorem linearElimination : MixedRunnerBlockTargets.LinearElimination := by
  intro i j hij lk rk e h k l a p ν
  exact LinearWindowProof.actualFiniteElimination i j hij lk rk e h k l a p ν
 theorem activeBounds : MixedRunnerBlockTargets.ActiveBounds :=
  ⟨ActiveHyperProof.actualCoefficientCollisionBound,ActiveHyperProof.actualGuardBound⟩
 theorem activeElimination : MixedRunnerBlockTargets.ActiveElimination := by
  intro i j kind e h k l q a p ν
  exact ActiveHyperProof.actualFiniteElimination i j kind e h k l q a p ν
private theorem finite_support (before : Matrix) (x bound name : Nat)
    (hm : name ∈ (Matrix.any ((List.range bound).map
      (fun n => before.substitute x (.numeral n)))).variables) :
    name ≠ x ∧ name ∈ before.variables := by
  rw [WindowProof.any_support] at hm
  obtain ⟨q,hq,hm⟩ := hm
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hq
  have hs := (WindowProof.matrix_support before (.numeral n) x name).mp hm
  simpa only [Term.variables,List.not_mem_nil,and_false,false_and,or_false,and_comm] using hs

 theorem reverseBlock : MixedRunnerBlockTargets.ReverseBlock := by
  intro xs i anchor e c p hi
  apply reduction_of_step
  · exact reverseElimination i anchor e c p hi
  · intro name hm
    obtain ⟨hne,ha|hp⟩ := ReverseWindowProof.exactSupportReduction i anchor e c p hi name hm
    · refine ⟨hne,?_⟩
      simp only [Matrix.variables,List.mem_append]
      apply Or.inl
      simp only [ReverseWindow.closeMatrix,shiftDomain,atMost,shiftTerm,
        Matrix.variables,Term.variables,List.mem_append,List.mem_singleton,List.not_mem_nil]
      tauto
    · exact ⟨hne,List.mem_append.mpr (Or.inr hp)⟩

 theorem linearBlock : MixedRunnerBlockTargets.LinearBlock := by
  intro xs i j hij lk rk e h k l a p
  apply reduction_of_step
  · exact linearElimination i j hij lk rk e h k l a p
  · intro name hm
    exact finite_support _ j _ name hm

 theorem activeBlock : MixedRunnerBlockTargets.ActiveBlock := by
  intro xs i j kind e h k l q a p
  apply reduction_of_step
  · exact activeElimination i j kind e h k l q a p
  · intro name hm
    exact finite_support _ j _ name hm

end LogicLineages.StandardControlCurrent.MixedRunnerBlockProof
