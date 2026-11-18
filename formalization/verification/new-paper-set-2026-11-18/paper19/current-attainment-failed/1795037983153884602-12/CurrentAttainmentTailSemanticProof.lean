module
public import LogicLineages.ControlSensitivityCurrent.CurrentAttainmentDataProof
public import LogicLineages.ControlSensitivityCurrent.FullStandardResiduesProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentAttainment

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open ExistentialPlan PrimitiveLowering
open InputNormalization (Input)

private theorem repeat_eval (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (n : Nat) {Γ : List Ty} (x a : Variable Γ .ground)
    (k : ∀ {Δ}, Renaming Γ Δ → Variable Δ .ground → Input Δ 0)
    (ρ : Variable Γ .ground → Nat) (P : Prop)
    (hk : ∀ (Δ : List Ty) (r : Renaming Γ Δ) (z : Variable Δ .ground)
      (ν : Variable Δ .ground → Nat), (∀ y, ν (r y) = ρ y) →
      ν z = ρ a + n * ρ x → ((k r z).eval p f ν Fin.elim0 ↔ P)) :
    (repeatAdd x a n k).eval p f ρ Fin.elim0 ↔ P := by
  induction n generalizing Γ with
  | zero =>
    exact hk Γ (fun x => x) a ρ (fun _ => rfl) (by simp)
  | succ n ih =>
    change (repeatAdd (.there x) .here n (fun r z => k (fun y => r (.there y)) z)).eval p f
      (extend ρ (ρ a + ρ x)) Fin.elim0 ↔ P
    apply ih
    intro Δ r z ν hr hz
    apply hk Δ (fun y => r (.there y)) z ν (fun y => hr (.there y))
    change ν z = ρ a + (n+1) * ρ x
    change ν z = ρ a + ρ x + n * ρ x at hz
    rw [hz, Nat.succ_mul]
    omega

theorem tail_eval (p : AdmissibleSum.Policy) (h : Unary) (c : Nat) (q : Request) :
    (∃ ρ, (tailProgram h c q).eval p Phi ρ Fin.elim0) ↔
      ∃ k y : Nat, SourceAST.callValue p Phi h (bound c q-c+q.1*k) = q.2.2.1*y + residue q := by
  have hpoint (ρ : Variable (List.replicate 2 Ty.ground) .ground → Nat) :
      (tailProgram h c q).eval p Phi ρ Fin.elim0 ↔
        SourceAST.callValue p Phi h (bound c q-c+q.1*ρ .here) = q.2.2.1*ρ (.there .here) + residue q := by
    unfold tailProgram
    rw [InputNormalization.Input.eval]
    apply repeat_eval
    intro Δ r a ν hν ha
    rw [InputNormalization.Input.eval, SourceAST.call_value, InputNormalization.Input.eval]
    apply repeat_eval
    intro Ξ s b μ hμ hb
    change (decide (μ (s (.there .here)) = μ b) = true) ↔ _
    rw [decide_eq_true_eq, hμ, hb]
    change (SourceAST.callValue p Phi h (ν a) =
      residue q + q.2.2.1 * ν (r (.there (.there .here)))) ↔ _
    rw [ha, hν, Nat.add_comm (residue q)]
    rfl
  constructor
  · rintro ⟨ρ,hρ⟩
    exact ⟨ρ .here,ρ (.there .here),(hpoint ρ).mp hρ⟩
  · rintro ⟨k,y,hky⟩
    let ρ : Variable (List.replicate 2 Ty.ground) .ground → Nat :=
      extend (extend (fun x : Variable [] .ground => nomatch x) y) k
    exact ⟨ρ,(hpoint ρ).mpr hky⟩

private theorem bound_ge (c : Nat) (q : Request) (hp : 0 < q.1) :
    max c (q.2.2.1 - 100) ≤ bound c q :=
  (Nat.le_mul_of_pos_right _ hp).trans (Nat.le_add_right _ _)

private theorem bound_mod (c : Nat) (q : Request) : Nat.ModEq q.1 (bound c q) q.2.1 := by
  unfold bound
  rw [Nat.mul_modulus_add_modEq_iff]
  exact Nat.mod_modEq _ _

private theorem endpoint_mod (l : NONote) (hl : Order.IsSuccLimit l.1.repr) (t m : Nat)
    (ht : actualOrdinalNorm l.1.repr ≤ t) (hm : 0 < m) (hthresh : m - 100 ≤ t) :
    Nat.ModEq m (actualHeadEndpoint l.1.repr t) (fastControlResidue m) := by
  obtain ⟨_, hd, _, _, hEnd, _⟩ :=
    actualHeadCompleteCount l.1.repr (normalRepresentationSound l) hl t ht
  have he : actualHeadCount l.1.repr t = (actualHeadCount l.1.repr t - 1) + 1 := by omega
  rw [hEnd]
  conv_lhs => rw [he, Function.iterate_succ_apply']
  apply FullStandardResidues.completeResidues.2.2.2 m hm
  exact hthresh.trans (iterate_index_mono (fun n => (self_lt_Phi n).le) t (Nat.zero_le _))

private theorem tail_numerical (l : NONote) (hl : Order.IsSuccLimit l.1.repr)
    (q : Request) (hm : 0 < q.2.2.1) (t : Nat) (ht : actualOrdinalNorm l.1.repr ≤ t)
    (hb : q.2.2.1-100 ≤ t) :
    Nat.ModEq q.2.2.1 (actualHeadCount l.1.repr t) q.2.2.2 ↔
      ∃ y, actualHeadValue l.1.repr t-1 = q.2.2.1*y+residue q := by
  let m := q.2.2.1
  let r := q.2.2.2
  let rm := fastControlResidue m
  let z := actualHeadEndpoint l.1.repr t
  let d := actualHeadCount l.1.repr t
  let v := actualHeadValue l.1.repr t-1
  let s := residue q
  change Nat.ModEq m d r ↔ ∃ y, v = m*y+s
  have hZ : Nat.ModEq m z rm := endpoint_mod l hl t m ht hm hb
  obtain ⟨_, hd, _, _, _, hv⟩ :=
    actualHeadCompleteCount l.1.repr (normalRepresentationSound l) hl t ht
  have e : v+1 = d+z := by dsimp [v,d,z]; omega
  have s_lt : s < m := Nat.mod_lt _ hm
  have s_eq : Nat.ModEq m (s+1) (r+rm) := by
    have hr := (Nat.mod_modEq (r+rm+(m-1)) m).add_right 1
    have h : r+rm+(m-1)+1 = r+rm+m := by omega
    rw [h, Nat.modEq_add_modulus_iff] at hr
    exact hr
  have middle : Nat.ModEq m d r ↔ Nat.ModEq m v s := by
    constructor
    · intro h
      apply Nat.ModEq.add_right_cancel' 1
      rw [e]
      exact (h.add hZ).trans s_eq.symm
    · intro h
      apply hZ.add_right_cancel
      rw [← e]
      exact (h.add_right 1).trans s_eq
  rw [middle]
  constructor
  · intro h
    have hvmod : v % m = s := by
      change v % m = s % m at h
      rwa [Nat.mod_eq_of_lt s_lt] at h
    refine ⟨v / m, ?_⟩
    have eq := Nat.mod_add_div v m
    rw [hvmod, Nat.add_comm] at eq
    exact eq.symm
  · rintro ⟨y,rfl⟩
    exact Nat.modulus_mul_add

theorem tail_correct (p : AdmissibleSum.Policy) (h : Unary)
    (l : NONote) (hl : Order.IsSuccLimit l.1.repr)
    (c : Nat) (hc : actualOrdinalNorm l.1.repr ≤ c)
    (hray : ∀ n, SourceAST.callValue p Phi h n = actualHeadValue l.1.repr (c+n)-1)
    (q : Request) (hp : 0 < q.1) (hm : 0 < q.2.2.1) :
    (∃ ρ, (tailProgram h c q).eval p Phi ρ Fin.elim0) ↔
      ∃ t, bound c q ≤ t ∧ AttainsAt l.1.repr q t := by
  let b := bound c q
  have hbc : c ≤ b := (le_max_left _ _).trans (bound_ge c q hp)
  have hbm : q.2.2.1 - 100 ≤ b := (le_max_right _ _).trans (bound_ge c q hp)
  have point (k : Nat) : (∃ y, SourceAST.callValue p Phi h (b-c+q.1*k) = q.2.2.1*y + residue q) ↔
      Nat.ModEq q.2.2.1 (actualHeadCount l.1.repr (b+q.1*k)) q.2.2.2 := by
    have he : c+(b-c+q.1*k) = b+q.1*k := by omega
    simp only [hray, he]
    exact (tail_numerical l hl q hm _ (hc.trans (hbc.trans (Nat.le_add_right _ _)))
      (hbm.trans (Nat.le_add_right _ _))).symm
  rw [tail_eval]
  constructor
  · rintro ⟨k,y,hky⟩
    have hkt : b ≤ b+q.1*k := Nat.le_add_right _ _
    refine ⟨b+q.1*k, hkt, hc.trans (hbc.trans hkt), ?_, (point k).mp ⟨y,hky⟩⟩
    exact Nat.add_modulus_mul_modEq_iff.mpr (bound_mod c q)
  · rintro ⟨t, hbt, ht, hq, hr⟩
    have hbq : Nat.ModEq q.1 b t := (bound_mod c q).trans hq.symm
    obtain ⟨k,rfl⟩ := (Nat.modEq_iff_exists_eq_add hbt).mp hbq
    obtain ⟨y,hy⟩ := (point k).mpr hr
    exact ⟨k,y,hy⟩

end LogicLineages.ControlSensitivityCurrent.CurrentAttainment
