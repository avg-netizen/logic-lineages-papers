module
public import LogicLineages.PermittedControl.ActualFiniteOrderBranchesTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFiniteOrderBranches
open OrdinalComparison.LayeredComparison.SnyatkovCompletion

private theorem linearMeaning (θ : Nat → Nat) (x y d : Nat) :
    (signedGap x y d).eval θ ↔ θ x + d ≤ θ y := by
  change 0 ≤ -(d : Int) + ((-1 : Int) * (θ x : Int) + (1 * (θ y : Int) + 0)) ↔ _
  simp only [neg_one_mul,one_mul,add_zero]
  omega

private theorem compareMeaning (θ : Nat → Nat) (a b : Entry) :
    (comparePair a b).eval θ ↔
      (a.2 = b.2 → θ a.1 = θ b.1) ∧ (a.2 < b.2 → θ a.1 < θ b.1) := by
  by_cases eq : a.2 = b.2
  · rw [comparePair,if_pos eq]
    change ((signedGap a.1 b.1 0).eval θ ∧ (signedGap b.1 a.1 0).eval θ) ↔ _
    rw [linearMeaning,linearMeaning]
    constructor
    · rintro ⟨lo,hi⟩
      refine ⟨fun _ => ?_,fun lt => ?_⟩
      · omega
      · exact (not_lt_of_ge eq.ge lt).elim
    · intro checks
      have same := checks.1 eq
      omega
  · by_cases lt : a.2 < b.2
    · rw [comparePair,if_neg eq,if_pos lt,linearMeaning]
      constructor
      · intro le
        exact ⟨fun h => (eq h).elim,fun _ => by omega⟩
      · intro checks
        have order := checks.2 lt
        omega
    · simp [comparePair,eq,lt,NormalForm.Formula.eval]

private theorem conjunctionMeaning (θ : Nat → Nat) (ps : List NormalForm.Formula) :
    (allTrue ps).eval θ ↔ ∀ q ∈ ps, q.eval θ := by
  induction ps with
  | nil => simp [allTrue,NormalForm.Formula.eval]
  | cons p ps ih =>
      change (p.eval θ ∧ (allTrue ps).eval θ) ↔ _
      rw [ih]
      constructor
      · rintro ⟨hp,hps⟩ q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hp
        · exact hps q hq
      · intro h
        exact ⟨h p List.mem_cons_self,fun q hq => h q (List.mem_cons_of_mem _ hq)⟩

theorem exactOrderGuard : ExactOrderGuard := by
  intro θ p
  have h := conjunctionMeaning θ (p.2.flatMap fun a => p.2.map (comparePair a))
  constructor
  · intro checked a ha b hb
    exact (compareMeaning θ a b).mp
      (h.mp checked _ (List.mem_flatMap.mpr ⟨a,ha,List.mem_map.mpr ⟨b,hb,rfl⟩⟩))
  · intro logic
    apply h.mpr
    intro q hq
    obtain ⟨a,ha,inMap⟩ := List.mem_flatMap.mp hq
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp inMap
    exact (compareMeaning θ a b).mpr (logic a ha b hb)

end LogicLineages.PermittedControl.ActualFiniteOrderBranches
