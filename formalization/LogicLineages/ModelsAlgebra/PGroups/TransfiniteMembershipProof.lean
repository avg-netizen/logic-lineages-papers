module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteMembershipTargets
public import LogicLineages.ModelsAlgebra.PGroups.PiConjunction
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryRenaming
public import LogicLineages.ModelsAlgebra.PGroups.ImageInfinitude
public import LogicLineages.ModelsAlgebra.PGroups.FiniteOmegaBoundProof
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTail
public import LogicLineages.ModelsAlgebra.PGroups.FiniteOrdinalFiltration
public import LogicLineages.ModelsAlgebra.PGroups.UlmFiniteIndependence
public import Mathlib.SetTheory.Cardinal.Ordinal
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth GroupInfinitary
universe u

private theorem append_zero {G : Type u} {n : ℕ} (a : Fin n → G) (c : Fin 0 → G) :
    append a c = a := by
  funext i
  change Fin.addCases a c (Fin.castAdd 0 i) = a i
  exact Fin.addCases_left _

private theorem pi_and_qf_realize (G : Type u) [AddCommGroup G] (n : ℕ)
    (φ : Formula n) (q : QF n) (a : Fin n → G) :
    (piAndQF φ q).Realize a ↔ φ.Realize a ∧ q.Realize a := by
  cases φ with
  | qf r => exact Iff.rfl
  | disjEx s m matrix =>
    exact (pi_conjunction_realization G n (.disjEx s m matrix) (piQF q) a).trans
      (and_congr Iff.rfl ((pi_qf_padding.{u,0} (1:Ordinal) one_ne_zero n q).2 G a))
  | conjAll s m matrix =>
    exact (pi_conjunction_realization G n (.conjAll s m matrix) (piQF q) a).trans
      (and_congr Iff.rfl ((pi_qf_padding.{u,0} (1:Ordinal) one_ne_zero n q).2 G a))

theorem pi_and_qf_exact : Targets.piAndQFExact.{u} := by
  intro α n φ q h
  refine ⟨?_,fun G _ a => pi_and_qf_realize G n φ q a⟩
  cases h with
  | qf side r => exact Complexity.qf .pi (.and r q)
  | pi hα s m matrix β lower rank =>
    exact pi_conjunction_complexity α hα n _ _
      (Complexity.pi hα s m matrix β lower rank) ((pi_qf_padding.{u,0} α hα n q).1)

private theorem countable_below (γ : Ordinal) [Countable γ.ToType]
    (β : Ordinal) (h : β ≤ γ) : Countable β.ToType := by
  apply Cardinal.mk_le_aleph0_iff.mp
  rw [Cardinal.mk_toType]
  exact (Ordinal.card_le_card h).trans (by
    simpa only [Cardinal.mk_toType] using (Cardinal.mk_le_aleph0 (α := γ.ToType)))

private theorem finite_tail_roots (G : Type u) [AddCommGroup G] (p : ℕ) (δ : Ordinal)
    (r : ℕ) (x : G) :
    x ∈ (transfiniteFiltration p (δ+r) : AddSubgroup G) ↔
      ∃ y : (transfiniteFiltration p δ : AddSubgroup G), p^r • (y:G)=x := by
  rw [← transfinite_tail_image,finite_ordinal_filtration,GroupInfinitary.finite_filtration_multiple_image]
  constructor
  · rintro ⟨z,⟨y,rfl⟩,hz⟩
    exact ⟨y,hz⟩
  · rintro ⟨y,hy⟩
    exact ⟨p^r • y,⟨y,rfl⟩,hy⟩

private theorem root_equation_realize (G : Type u) [AddCommGroup G] (p r n : ℕ)
    (t : GroupTerm n) (a : Fin n → G) (d : Fin 1 → G) :
    (rootEquation p r n t).Realize (append a d) ↔ p^r • d 0 = t.eval a := by
  change (multipleTerm (p^r) (.var (Fin.natAdd n 0))).eval (append a d) =
    (renameTerm (Fin.castAdd 1) t).eval (append a d) ↔ _
  rw [multiple_term_evaluation,term_renaming_evaluation]
  have ha : (fun i => append a d (Fin.castAdd 1 i)) = a := by
    funext i; exact Fin.addCases_left _
  rw [ha]
  simp only [GroupTerm.eval,append,Fin.addCases_right]

private theorem root_formula (p : ℕ) (δ α : Ordinal.{0}) (r n : ℕ) (t : GroupTerm n)
    (φ : Formula (n+1)) (hφ : Complexity .pi α φ)
    (hsem : ∀ (G : Type u) [AddCommGroup G] (a : Fin (n+1) → G),
      φ.Realize a ↔ a (Fin.natAdd n 0) ∈ (transfiniteFiltration p δ : AddSubgroup G)) :
    ∃ ψ : Formula n, Complexity .sigma (α+1) ψ ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
        ψ.Realize a ↔ t.eval a ∈ (transfiniteFiltration p (δ+r) : AddSubgroup G) := by
  let matrix := piAndQF φ (rootEquation p r n t)
  let ψ : Formula n := countableDisjEx (fun _ : Unit => 1) (fun _ => matrix)
  refine ⟨ψ,countable_disj_ex_complexity (α+1) (ne_of_gt (lt_of_le_of_lt zero_le (Order.lt_succ α)))
    Unit n (fun _ => 1) (fun _ => matrix) (fun _ => α) (fun _ => Order.lt_succ α)
    (fun _ => (pi_and_qf_exact.{u} α (n+1) φ (rootEquation p r n t) hφ).1),?_⟩
  intro G _ a
  rw [countable_disj_ex_realization,finite_tail_roots]
  constructor
  · rintro ⟨_,d,hd⟩
    obtain ⟨hy,he⟩ := (pi_and_qf_realize G (n+1) φ (rootEquation p r n t) (append a d)).mp hd
    have hy' : d 0 ∈ (transfiniteFiltration p δ : AddSubgroup G) := by
      simpa only [append,Fin.addCases_right] using (hsem G (append a d)).mp hy
    exact ⟨⟨d 0,hy'⟩,(root_equation_realize G p r n t a d).mp he⟩
  · rintro ⟨y,hy⟩
    refine ⟨(),fun _ => (y:G),?_⟩
    apply (pi_and_qf_realize G (n+1) φ (rootEquation p r n t) _).mpr
    refine ⟨(hsem G _).mpr ?_,(root_equation_realize G p r n t a _).mpr hy⟩
    simpa only [append,Fin.addCases_right] using y.property

private theorem sigma_pad (α : Ordinal.{0}) (n : ℕ) (φ : Formula n) (hφ : Complexity .pi α φ) :
    ∃ ψ : Formula n, Complexity .sigma (α+1) ψ ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G), ψ.Realize a ↔ φ.Realize a := by
  let ψ : Formula n := countableDisjEx (fun _ : Unit => 0) (fun _ => φ)
  refine ⟨ψ,countable_disj_ex_complexity (α+1)
    (ne_of_gt (lt_of_le_of_lt zero_le (Order.lt_succ α))) Unit n _ _ (fun _ => α)
    (fun _ => Order.lt_succ α) (fun _ => hφ),?_⟩
  intro G _ a
  rw [countable_disj_ex_realization]
  constructor
  · rintro ⟨_,d,h⟩; simpa only [append_zero] using h
  · intro h; exact ⟨(),Fin.elim0,by simpa only [append_zero] using h⟩

theorem omega_block_membership_definable : Targets.omegaBlockMembershipDefinable.{u} := by
  classical
  intro p γ
  induction γ using WellFoundedLT.induction with
  | ind γ ih =>
    intro _ n t
    rcases Ordinal.zero_or_succ_or_isSuccLimit γ with hz | ⟨β,hβ⟩ | hγ
    · subst γ
      refine ⟨.qf (.equal t t),by simpa only [mul_zero] using Complexity.qf .pi (.equal t t),?_⟩
      intro G _ a
      simp only [Formula.Realize,QF.Realize,mul_zero,transfiniteFiltration_zero,AddSubgroup.mem_top,iff_true]
    · subst γ
      letI : Countable β.ToType := countable_below (Order.succ β) β (Order.le_succ β)
      obtain ⟨φ,hφ,hsem⟩ := ih β (Order.lt_succ β) (n+1) (.var (Fin.natAdd n 0))
      have hex (r : ℕ) := root_formula p (Ordinal.omega0*β) (2*β) r n t φ hφ hsem
      choose ψ hψ hψsem using hex
      let Φ : Formula n := countableConjAll (fun _ : ℕ => 0) (fun r => ψ r)
      have hΦ : Complexity .pi ((2*β+1)+1) Φ := countable_conj_all_complexity _
        (ne_of_gt (lt_of_le_of_lt zero_le (Order.lt_succ (2*β+1)))) ℕ n _ _ (fun _ => 2*β+1)
        (fun _ => Order.lt_succ _) hψ
      refine ⟨Φ,by simpa only [Order.succ_eq_add_one,mul_add_one,add_assoc,one_add_one_eq_two] using hΦ,?_⟩
      intro G _ a
      rw [Order.succ_eq_add_one,mul_add_one,omega_block_filtration]
      rw [AddSubgroup.mem_iInf,countable_conj_all_realization]
      constructor
      · intro h r
        exact (hψsem r G a).mp (by simpa only [append_zero] using h r Fin.elim0)
      · intro h r d
        simpa only [append_zero] using (hψsem r G a).mpr (h r)
    · let β (i : γ.ToType) : Ordinal := Ordinal.typein (α := γ.ToType) (· < ·) i
      have hβ (i : γ.ToType) : β i < γ := Ordinal.typein_lt_self i
      have hex (i : γ.ToType) : ∃ φ : Formula n, Complexity .pi (2*β i) φ ∧
          ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
            φ.Realize a ↔ t.eval a ∈ (transfiniteFiltration p (Ordinal.omega0*β i) : AddSubgroup G) := by
        letI := countable_below γ (β i) (hβ i).le
        exact ih (β i) (hβ i) n t
      choose φ hφ hsem using hex
      have hpads (i : γ.ToType) := sigma_pad (2*β i) n (φ i) (hφ i)
      choose ψ hψ hψsem using hpads
      let Φ : Formula n := countableConjAll (fun _ : γ.ToType => 0) (fun i => ψ i)
      have hlt (i : γ.ToType) : 2*β i+1 < 2*γ := by
        have hle := (Ordinal.isNormal_mul_right (by norm_num : (0:Ordinal)<2)).monotone
          (Order.add_one_le_iff.mpr (hβ i))
        have hh : 2*β i+1 < 2*(β i+1) := by
          rw [mul_add_one]
          exact (add_lt_add_iff_left _).mpr one_lt_two
        exact hh.trans_le hle
      refine ⟨Φ,countable_conj_all_complexity (2*γ) (mul_ne_zero (by simp) hγ.ne_zero)
        γ.ToType n _ _ (fun i => 2*β i+1) hlt hψ,?_⟩
      intro G _ a
      rw [countable_conj_all_realization]
      constructor
      · intro h
        rw [transfiniteFiltration_limit p (Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0
          (lt_of_le_of_ne zero_le (Ne.symm hγ.ne_zero)))]
        apply AddSubgroup.mem_iInf.mpr
        intro ξ
        obtain ⟨ζ,hζ,hξ⟩ := (Ordinal.lt_mul_iff_of_isSuccLimit hγ).mp ξ.property
        obtain ⟨i,hi⟩ := Ordinal.typein_surj (α := γ.ToType) (· < ·) (by simpa using hζ)
        have hm : t.eval a ∈ (transfiniteFiltration p (Ordinal.omega0*β i) : AddSubgroup G) :=
          (hsem i G a).mp ((hψsem i G a).mp (by simpa only [append_zero] using h i Fin.elim0))
        have he : β i = ζ := hi
        rw [he] at hm
        exact transfiniteFiltration_antitone p hξ.le hm
      · intro h i d
        apply (hψsem i G _).mpr
        apply (hsem i G _).mpr
        rw [append_zero]
        exact transfiniteFiltration_antitone p
          ((Ordinal.isNormal_mul_right Ordinal.omega0_pos).monotone (hβ i).le) h

theorem finite_offset_membership_definable : Targets.finiteOffsetMembershipDefinable.{u} := by
  intro p γ _ r n t
  obtain ⟨φ,hφ,hsem⟩ := omega_block_membership_definable p γ (n+1) (.var (Fin.natAdd n 0))
  exact root_formula p (Ordinal.omega0*γ) (2*γ) r n t φ hφ hsem
end LogicLineages.ModelsAlgebra.PGroups
