module

public import LogicLineages.ModelsAlgebra.PGroups.FiniteImageTableTargets
public import LogicLineages.ModelsAlgebra.PGroups.ImageCardinality

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

open GroupBackAndForth
universe u v w

theorem table_term_evaluation : Targets.groupTableTermEvaluation.{u,w} := by
  intro K _ _ G _ c n a d x
  unfold tableTerm
  rw [multiple_term_evaluation G (n + Fintype.card K) c]
  simp only [GroupTerm.eval, append, Fin.addCases_right]

theorem finite_image_table_matrix : Targets.groupFiniteImageTableMatrix.{u,w} := by
  intro K _ _ G _ c n a d
  let e := Fintype.equivFin K
  simp only [finiteImageTableMatrix, QF.Realize,
    distinct_multiple_matrix_realization G c n (Fintype.card K),
    finite_conjunction_realization G (n + Fintype.card K) (Fintype.card K),
    GroupTerm.eval, table_term_evaluation K G c n a d]
  constructor
  · rintro ⟨hinj, hzero, hneg, hadd⟩
    refine ⟨hinj.comp e.injective, hzero, ?_, ?_⟩
    · intro x
      simpa only [e, Equiv.symm_apply_apply] using hneg (e x)
    · intro x y
      simpa only [e, Equiv.symm_apply_apply] using hadd (e x) (e y)
  · rintro ⟨hinj, hzero, hneg, hadd⟩
    refine ⟨?_, hzero, ?_, ?_⟩
    · intro i j hij
      apply e.symm.injective
      apply hinj
      simpa only [e, Equiv.apply_symm_apply] using hij
    · intro i
      exact hneg (e.symm i)
    · intro i j
      exact hadd (e.symm i) (e.symm j)

theorem finite_image_table_formula : Targets.groupFiniteImageTableFormula.{u,v,w} := by
  intro K _ _ c n
  constructor
  · exact Complexity.sigma one_ne_zero {0} (fun _ => Fintype.card K)
      (fun _ => .qf (finiteImageTableMatrix K c n)) (fun _ => 0)
      (fun _ => zero_lt_one) (fun _ => Complexity.qf .pi _)
  · intro G _ a
    classical
    let e := Fintype.equivFin K
    change (∃ i : ({0} : Set ℕ), ∃ d : Fin (Fintype.card K) → G,
      (finiteImageTableMatrix K c n).Realize (append a d)) ↔ _
    constructor
    · rintro ⟨i, d, hd⟩
      have hv := (finite_image_table_matrix K G c n a d).mp hd
      let f : K →+ multipleImage G c :=
        { toFun := fun x => ⟨c • d (e x), ⟨d (e x), rfl⟩⟩
          map_zero' := Subtype.ext hv.2.1
          map_add' := fun x y => Subtype.ext (hv.2.2.2 x y) }
      refine ⟨f, ?_⟩
      intro x y hxy
      exact hv.1 (congrArg Subtype.val hxy)
    · rintro ⟨f, hf⟩
      choose d hd using fun i : Fin (Fintype.card K) => (f (e.symm i)).property
      have hvalue : ∀ x : K, c • d (Fintype.equivFin K x) = (f x : G) := by
        intro x
        simpa only [e, Equiv.symm_apply_apply, nsmulAddMonoidHom_apply] using hd (e x)
      refine ⟨⟨0, by simp⟩, d, (finite_image_table_matrix K G c n a d).mpr ?_⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x y hxy
        apply hf
        apply Subtype.ext
        simpa only [hvalue] using hxy
      · dsimp only
        rw [hvalue]
        exact congrArg Subtype.val f.map_zero
      · intro x
        dsimp only
        rw [hvalue, hvalue]
        exact congrArg Subtype.val (f.map_neg x)
      · intro x y
        dsimp only
        rw [hvalue, hvalue, hvalue]
        exact congrArg Subtype.val (f.map_add x y)

theorem finite_image_isomorphism_formula : Targets.groupFiniteImageIsomorphismFormula.{u,v,w} := by
  intro K _ _ c
  constructor
  · exact ⟨(finite_image_table_formula.{u,v,w} K c 0).1,
      (bounded_multiple_image_formula.{u,v} c (Fintype.card K)).1⟩
  · intro G _
    classical
    let R := multipleImage G c
    change ((finiteImageTableFormula K c 0).Realize (Fin.elim0 : Fin 0 → G) ∧
      (boundedMultipleImage c (Fintype.card K)).Realize (Fin.elim0 : Fin 0 → G)) ↔ _
    rw [(finite_image_table_formula.{u,v,w} K c 0).2 G Fin.elim0,
      (bounded_multiple_image_formula.{u,v} c (Fintype.card K)).2 G]
    change ((∃ f : K →+ R, Function.Injective f) ∧ Finite R ∧ Nat.card R ≤ Fintype.card K) ↔
      Nonempty (R ≃+ K)
    constructor
    · rintro ⟨⟨f, hf⟩, hfinite, hupper⟩
      letI : Finite R := hfinite
      letI : Fintype R := Fintype.ofFinite R
      have hlower := Fintype.card_le_of_injective f hf
      have heq : Fintype.card K = Fintype.card R :=
        Nat.le_antisymm hlower (by simpa only [Nat.card_eq_fintype_card] using hupper)
      have hbij : Function.Bijective f :=
        (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, heq⟩
      exact ⟨(AddEquiv.ofBijective f hbij).symm⟩
    · rintro ⟨e⟩
      letI : Finite R := Finite.of_equiv K e.symm.toEquiv
      refine ⟨⟨e.symm.toAddMonoidHom, e.symm.injective⟩, inferInstance, ?_⟩
      have heq := Nat.card_congr e.toEquiv
      simpa only [Nat.card_eq_fintype_card] using heq.le

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
