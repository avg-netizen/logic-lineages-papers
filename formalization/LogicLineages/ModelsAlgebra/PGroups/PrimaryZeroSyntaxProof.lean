module
public import LogicLineages.ModelsAlgebra.PGroups.PrimaryZeroSyntaxTargets
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteMembershipProof
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryDual
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth GroupInfinitary
universe u

private theorem append_zero {G : Type u} {n : ℕ} (a : Fin n → G) (c : Fin 0 → G) :
    append a c = a := by
  funext i
  change Fin.addCases a c (Fin.castAdd 0 i) = a i
  exact Fin.addCases_left _

theorem primary_sentence_exact : Targets.primarySentenceExact.{u} := by
  intro p
  have hw : Complexity .sigma (1:Ordinal) (primaryWitness p) :=
    countable_disj_ex_complexity 1 one_ne_zero ℕ 1 (fun _ => 0) _ (fun _ => 0)
      (fun _ => zero_lt_one) (fun k => Complexity.qf .pi (.equal (multipleTerm (p^k) (.var 0)) .zero))
  refine ⟨countable_conj_all_complexity 2 two_ne_zero Unit 0 (fun _ => 1) _ (fun _ => 1)
    (fun _ => one_lt_two) (fun _ => hw),?_⟩
  have hsem (G : Type u) [AddCommGroup G] (a : Fin 1 → G) :
      (primaryWitness p).Realize a ↔ ∃ k : ℕ, p^k • a 0=0 := by
    rw [primaryWitness,countable_disj_ex_realization]
    simp only [Formula.Realize,QF.Realize,multiple_term_evaluation,GroupTerm.eval,append_zero]
    constructor
    · rintro ⟨k,_,hk⟩
      rw [multiple_term_evaluation] at hk
      exact ⟨k,hk⟩
    · rintro ⟨k,hk⟩
      refine ⟨k,Fin.elim0,?_⟩
      rw [multiple_term_evaluation]
      exact hk
  intro G _
  rw [primarySentence,countable_conj_all_realization]
  constructor
  · intro h x
    have hx := (hsem G (append Fin.elim0 (fun _ : Fin 1 => x))).mp (h () (fun _ => x))
    exact hx
  · intro h _ d
    exact (hsem G _).mpr (h _)

private theorem bounded_tail_zero (G : Type u) [AddCommGroup G] (p : ℕ) (δ : Ordinal.{0}) (N : ℕ) :
    (∀ x : (transfiniteFiltration p δ : AddSubgroup G), p^N • x=0) ↔
      (transfiniteFiltration p (δ+N) : AddSubgroup G) = ⊥ := by
  let S : AddSubgroup G := transfiniteFiltration p δ
  constructor
  · intro h
    have hz : (transfiniteFiltration p (N:Ordinal) : AddSubgroup S) = ⊥ := by
      rw [finite_ordinal_filtration,GroupInfinitary.finite_filtration_multiple_image]
      apply le_antisymm
      · rintro x ⟨y,rfl⟩; exact h y
      · exact bot_le
    rw [← transfinite_tail_image,hz,AddSubgroup.map_bot]
  · intro h x
    have hm : p^N • x ∈ (transfiniteFiltration p (N:Ordinal) : AddSubgroup S) := by
      rw [finite_ordinal_filtration,GroupInfinitary.finite_filtration_multiple_image]
      exact ⟨x,rfl⟩
    have hx := (transfinite_tail_membership G p δ (N:Ordinal) (p^N • x)).mp hm
    exact Subtype.ext (h.le hx)

theorem zero_stage_descriptor : Targets.zeroStageDescriptor.{u} := by
  intro p γ _ N
  obtain ⟨φ,hφ,hsem⟩ := omega_block_membership_definable.{u} p γ 1 (.var 0)
  let q : QF 1 := .neg (.equal (multipleTerm (p^N) (.var 0)) .zero)
  let counter : Formula 0 := countableDisjEx (fun _ : Unit => 1) (fun _ => piAndQF φ q)
  have hc : Complexity .sigma (2*γ+1) counter := countable_disj_ex_complexity _
    (ne_of_gt (lt_of_le_of_lt zero_le (Order.lt_succ (2*γ)))) Unit 0 (fun _ => 1) _
    (fun _ => 2*γ) (fun _ => Order.lt_succ _) (fun _ => (pi_and_qf_exact.{u} _ _ _ _ hφ).1)
  refine ⟨counter.dual,dual_complexity .sigma _ _ _ hc,?_⟩
  intro G _
  let S : AddSubgroup G := transfiniteFiltration p (Ordinal.omega0*γ)
  have hcounter : counter.Realize (Fin.elim0 : Fin 0 → G) ↔
      ∃ x : G, x ∈ S ∧ p^N • x ≠ 0 := by
    rw [countable_disj_ex_realization]
    constructor
    · rintro ⟨_,d,hd⟩
      obtain ⟨hm,hq⟩ := ((pi_and_qf_exact.{u} _ _ _ _ hφ).2 G _).mp hd
      have hmem := (hsem G (append Fin.elim0 d)).mp hm
      change d 0 ∈ S at hmem
      change ¬ ((multipleTerm (p^N) (.var 0)).eval (append Fin.elim0 d) = 0) at hq
      rw [multiple_term_evaluation] at hq
      exact ⟨d 0,hmem,hq⟩
    · rintro ⟨x,hx,hne⟩
      refine ⟨(),fun _ => x,?_⟩
      apply ((pi_and_qf_exact.{u} _ _ _ _ hφ).2 G _).mpr
      refine ⟨(hsem G _).mpr hx,?_⟩
      change ¬ ((multipleTerm (p^N) (.var 0)).eval (append Fin.elim0 (fun _ : Fin 1 => x)) = 0)
      rw [multiple_term_evaluation]
      exact hne
  rw [dual_realization,hcounter,← bounded_tail_zero G p (Ordinal.omega0*γ) N]
  constructor
  · intro h x
    apply Subtype.ext
    by_contra hx
    exact h ⟨x,x.property,hx⟩
  · intro h
    rintro ⟨x,hx,hne⟩
    exact hne (congrArg (fun z : S => (z:G)) (h ⟨x,hx⟩))
end LogicLineages.ModelsAlgebra.PGroups
