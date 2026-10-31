module
public import LogicLineages.OrdinalComparison.WWAdmissibleExpansionTargets
public import LogicLineages.OrdinalComparison.WWAdmissibleSumProof
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AdmissibleExpansion
open AdmissibleSum AdmissiblePartial
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

private theorem nodes_pos {ι : Type} (t : LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term ι) : 0 < ordinalLiteralNodes t := by
  cases t <;> simp [ordinalLiteralNodes] <;> omega

private theorem nodes_headClosure {Γ : List Ty} {σ : Ty}
    (t : OrdinalExpression (σ :: Γ)) :
    ordinalLiteralNodes (ordinalHeadClosure t) = ordinalLiteralNodes t := by
  induction t with
  | var c =>
    rcases c with ⟨τ, v, i⟩
    cases v <;> rfl
  | zero | one | omega => rfl
  | add f g hf hg | emul f g hf hg | collapse f g hf hg =>
    change ordinalLiteralNodes (ordinalHeadClosure f) + ordinalLiteralNodes (ordinalHeadClosure g) + 1 = _
    rw [hf, hg]
    rfl

private theorem linear_budget (n : Nat) : n + 2 ≤ 6 * 3 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hp : 0 < 3 ^ n := Nat.pow_pos (by omega)
    omega

private theorem binary_budget (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    2 * (6 * 3 ^ a) + 6 * 3 ^ b + 4 ≤ 6 * 3 ^ (a + b + 1) := by
  have hA : 3 ≤ 3 ^ a := by
    simpa using (Nat.pow_le_pow_right (n := 3) (by omega) ha)
  have hB : 3 ≤ 3 ^ b := by
    simpa using (Nat.pow_le_pow_right (n := 3) (by omega) hb)
  rw [pow_succ, pow_add]
  have hABa := Nat.mul_le_mul_left (3 ^ a) hB
  have hABb := Nat.mul_le_mul_right (3 ^ b) hA
  nlinarith

private theorem three_nodes {Γ : List Ty} (p : Policy) (site : MacroSite)
    (a b c : OrdinalExpression Γ) :
    ordinalLiteralNodes (three p site a b c) =
      ordinalLiteralNodes a + ordinalLiteralNodes b + ordinalLiteralNodes c + 2 := by
  have h := (actualAdmissibleSumSyntax Γ 3 (p.shape site 2)
    (fun i => if i.val = 0 then a else if i.val = 1 then b else c)).2.2
  change ordinalLiteralNodes (three p site a b c) + 1 =
    ordinalLiteralNodes a + (ordinalLiteralNodes b + (ordinalLiteralNodes c + 0)) + 3 at h
  unfold three at h ⊢
  omega

private theorem twice_nodes {Γ : List Ty} (p : Policy) (a : OrdinalExpression Γ) :
    ordinalLiteralNodes (twice p a) = 2 * ordinalLiteralNodes a + 1 := by
  have h := (actualAdmissibleSumSyntax Γ 2 (p.shape .positiveRepeat 1) (fun _ => a)).2.2
  change ordinalLiteralNodes (twice p a) + 1 =
    ordinalLiteralNodes a + (ordinalLiteralNodes a + 0) + 2 at h
  unfold twice at h ⊢
  omega

private theorem free_bound {Γ : List Ty} {σ : Ty} (p : Policy) (i : Nat)
    (t : OrdinalExpression (σ :: Γ)) (hf : ordinalHeadFree t = true)
    (v : OrdinalPartialVector Γ σ) (hv : run p i t = some v) :
    ∀ j, ordinalLiteralNodes (v j) ≤ 6 * 3 ^ ordinalLiteralNodes t := by
  rw [run.eq_def, hf] at hv
  have he : ordinalFreePartialVector i t = v := Option.some.inj hv
  subst v
  intro j
  unfold ordinalFreePartialVector
  split
  · simpa only [ordinalLiteralNodes, nodes_headClosure, Nat.add_assoc] using
      linear_budget (ordinalLiteralNodes t)
  · have := linear_budget (ordinalLiteralNodes t)
    simp only [ordinalLiteralNodes]
    omega

theorem actualAdmissiblePartialExpansion : Targets.ActualAdmissiblePartialExpansion := by
  intro Γ σ p i t
  induction t generalizing i with
  | zero => intro v hv; exact free_bound p i .zero rfl v hv
  | one => intro v hv; exact free_bound p i .one rfl v hv
  | omega => intro v hv; exact free_bound p i .omega rfl v hv
  | var c =>
    intro v hv
    by_cases hf : ordinalHeadFree (.var c) = true
    · exact free_bound p i (.var c) hf v hv
    · rcases c with ⟨τ, x, k⟩
      rw [run, Bool.eq_false_iff.mpr hf] at hv
      by_cases hi : i = k.val
      · simp only [Bool.false_eq_true, if_false, hi, if_true] at hv
        have he : (fun _ => Term.one) = v := Option.some.inj hv
        subst v
        intro j
        simp [ordinalLiteralNodes]
      · simp [hi] at hv
  | add f g ihf ihg =>
    intro v hv
    by_cases hf : ordinalHeadFree (.add f g) = true
    · exact free_bound p i (.add f g) hf v hv
    · rw [run, Bool.eq_false_iff.mpr hf] at hv
      have hex : ∃ pf : OrdinalPartialVector Γ σ,
          run p i f = some pf ∧ ∃ pg : OrdinalPartialVector Γ σ,
          run p i g = some pg ∧
          (fun j => three p .activeAdd (pf j) (pg j) .one) = v := by
        simpa only [Bool.false_eq_true, if_false, bind, pure,
          Option.bind_eq_some_iff, Option.some.injEq] using hv
      obtain ⟨pf, hpf, pg, hpg, hv⟩ := hex
      subst v
      intro j
      have af := ihf i pf hpf j
      have ag := ihg i pg hpg j
      have bd := binary_budget _ _ (nodes_pos f) (nodes_pos g)
      simp only [three_nodes, ordinalLiteralNodes]
      omega
  | emul f g ihf ihg =>
    intro v hv
    by_cases hf : ordinalHeadFree (.emul f g) = true
    · exact free_bound p i (.emul f g) hf v hv
    · rw [run, Bool.eq_false_iff.mpr hf] at hv
      by_cases hi : 0 < i
      · rw [if_pos hi] at hv
        have hex : ∃ pf : OrdinalPartialVector Γ σ,
            run p (i + 1) f = some pf ∧ ∃ pg : OrdinalPartialVector Γ σ,
            run p i g = some pg ∧
            (fun j => three p .activeExp (twice p (pf j)) (pg j) .one) = v := by
          simpa only [Bool.false_eq_true, if_false, bind, pure,
            Option.bind_eq_some_iff, Option.some.injEq] using hv
        obtain ⟨pf, hpf, pg, hpg, hv⟩ := hex
        subst v
        intro j
        have af := ihf (i + 1) pf hpf j
        have ag := ihg i pg hpg j
        have bd := binary_budget _ _ (nodes_pos f) (nodes_pos g)
        simp only [three_nodes, twice_nodes, ordinalLiteralNodes]
        omega
      · simp [hi] at hv
  | collapse f g ihf ihg =>
    intro v hv
    by_cases hf : ordinalHeadFree (.collapse f g) = true
    · exact free_bound p i (.collapse f g) hf v hv
    · rw [run, Bool.eq_false_iff.mpr hf] at hv
      by_cases hi : i = 0
      · rw [if_pos hi] at hv
        have hex : ∃ pf : OrdinalPartialVector Γ σ,
            run p 1 f = some pf ∧ ∃ pg : OrdinalPartialVector Γ σ,
            run p 0 g = some pg ∧
            (fun j => if j.val = 0 then .collapse (ordinalHeadClosure f) (pg 0)
              else .add (pf j) (pg j)) = v := by
          simpa only [Bool.false_eq_true, if_false, bind, pure,
            Option.bind_eq_some_iff, Option.some.injEq] using hv
        obtain ⟨pf, hpf, pg, hpg, hv⟩ := hex
        subst v
        intro j
        have bd := binary_budget _ _ (nodes_pos f) (nodes_pos g)
        by_cases hj : j.val = 0
        · have ag := ihg 0 pg hpg 0
          have af := linear_budget (ordinalLiteralNodes f)
          simp only [if_pos hj, ordinalLiteralNodes, nodes_headClosure]
          omega
        · have af := ihf 1 pf hpf j
          have ag := ihg 0 pg hpg j
          simp only [if_neg hj, ordinalLiteralNodes]
          omega
      · simp [hi] at hv

theorem actualAdmissibleRepeatExpansion : Targets.ActualAdmissibleRepeatExpansion := by
  intro Γ p site k hk t
  cases k with
  | zero => omega
  | succ k =>
    have h := (actualAdmissibleSumSyntax Γ (k + 1) (p.shape site k) (fun _ => t)).2.2
    simpa [AdmissibleAssignment.repeated, List.ofFn_const, Nat.mul_add, Nat.add_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

theorem actualLiteralBoxExpansion : Targets.ActualLiteralBoxExpansion := by
  intro Γ n f g i hi hin
  rw [ordinalBoxPositive, dif_pos hin]
  simp only [ordinalLiteralNodes]
  omega

end LogicLineages.OrdinalComparison.Source.AdmissibleExpansion
