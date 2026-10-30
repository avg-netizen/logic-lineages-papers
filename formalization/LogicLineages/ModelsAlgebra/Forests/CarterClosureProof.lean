module

public import LogicLineages.ModelsAlgebra.Forests.CarterClosureTargets
public import LogicLineages.ModelsAlgebra.Forests.CarterAutomataProof

/-! Total deterministic products/complements pay all closure and equivalence
claims, including symmetry invariance for the unordered source convention. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.CarterClosureProof

open CarterAutomata CarterAutomataProof

theorem carterProductRun : Targets.CarterProductRun := by
  intro k q r mode M N t
  induction t with
  | leaf a => simp [run, productMachine]
  | node a l r ihl ihr =>
      change finProdFinEquiv.symm (finProdFinEquiv
        (M.nodeState a (finProdFinEquiv.symm (run (productMachine mode M N) l)).1
          (finProdFinEquiv.symm (run (productMachine mode M N) r)).1,
         N.nodeState a (finProdFinEquiv.symm (run (productMachine mode M N) l)).2
          (finProdFinEquiv.symm (run (productMachine mode M N) r)).2)) = _
      rw [Equiv.symm_apply_apply, ihl, ihr]
      rfl

private theorem run_complement {k q} (M : Automaton k q) (t : BinaryLabelTree k) :
    run (complementMachine M) t = run M t := by
  induction t with
  | leaf a => rfl
  | node a l r ihl ihr =>
      change M.nodeState a (run (complementMachine M) l) (run (complementMachine M) r) = _
      rw [ihl, ihr]
      rfl

theorem carterComplementLanguage : Targets.CarterComplementLanguage := by
  intro k q M t
  change run (complementMachine M) t ∈ Finset.univ \ M.accepting ↔ _
  rw [run_complement]
  simp [accepts]

private theorem product_accepts {k q r} (mode : Bool → Bool → Bool)
    (M : Automaton k q) (N : Automaton k r) (t : BinaryLabelTree k) :
    accepts (productMachine mode M N) t ↔
      mode (decide (run M t ∈ M.accepting)) (decide (run N t ∈ N.accepting)) = true := by
  change run (productMachine mode M N) t ∈ Finset.univ.filter _ ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [carterProductRun k q r mode M N t]

theorem carterIntersectionLanguage : Targets.CarterIntersectionLanguage := by
  intro k q r M N t
  simpa only [intersectionMachine, Bool.and_eq_true, decide_eq_true_eq, accepts]
    using product_accepts Bool.and M N t

theorem carterUnionLanguage : Targets.CarterUnionLanguage := by
  intro k q r M N t
  simpa only [unionMachine, Bool.or_eq_true, decide_eq_true_eq, accepts]
    using product_accepts Bool.or M N t

theorem carterDifferenceLanguage : Targets.CarterDifferenceLanguage := by
  intro k q r M N t
  rw [symmetricDifferenceMachine, product_accepts]
  by_cases hm : run M t ∈ M.accepting <;> by_cases hn : run N t ∈ N.accepting <;>
    simp [accepts, hm, hn]

theorem carterLanguageEquivalence : Targets.CarterLanguageEquivalence := by
  classical
  intro k q r M N
  rw [languageEquivalent, carterLanguageEmptiness]
  constructor
  · intro h t
    by_contra ht
    exact h ⟨t, (carterDifferenceLanguage k q r M N t).mpr ht⟩
  · rintro h ⟨t, ht⟩
    exact (carterDifferenceLanguage k q r M N t).mp ht (h t)

theorem carterComplementSymmetric : Targets.CarterComplementSymmetric := by
  intro k q M h
  exact h

theorem carterProductSymmetric : Targets.CarterProductSymmetric := by
  intro k q r mode M N hm hn a x y
  change finProdFinEquiv
    (M.nodeState a (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm y).1,
     N.nodeState a (finProdFinEquiv.symm x).2 (finProdFinEquiv.symm y).2) = _
  rw [hm a (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm y).1,
    hn a (finProdFinEquiv.symm x).2 (finProdFinEquiv.symm y).2]
  rfl

end LogicLineages.ModelsAlgebra.Forests.CarterClosureProof
