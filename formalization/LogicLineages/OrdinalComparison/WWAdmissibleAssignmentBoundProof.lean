module
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentBoundTargets
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentProof
public import LogicLineages.OrdinalComparison.WWAdmissibleExpansionProof
public import LogicLineages.OrdinalComparison.WWLiteralSizeProof
public import Mathlib.Tactic.Linarith

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AdmissibleAssignmentBound
open AdmissibleSum AdmissibleAssignment AdmissibleExpansion
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

private theorem nodes_pos {Γ : List Ty} (t : OrdinalExpression Γ) :
    0 < ordinalLiteralNodes t := by
  cases t <;> simp [ordinalLiteralNodes] <;> omega

private theorem nodes_headClosure {Γ : List Ty} {σ : Ty}
    (t : OrdinalExpression (σ :: Γ)) :
    ordinalLiteralNodes (ordinalHeadClosure t) = ordinalLiteralNodes t := by
  induction t with
  | var c => rcases c with ⟨τ, v, i⟩; cases v <;> rfl
  | zero | one | omega => rfl
  | add f g hf hg | emul f g hf hg | collapse f g hf hg =>
    change ordinalLiteralNodes (ordinalHeadClosure f) + ordinalLiteralNodes (ordinalHeadClosure g) + 1 = _
    rw [hf, hg]
    rfl

private theorem sum_bound (n E : Nat) (f : Fin n → Nat) (h : ∀ i, f i ≤ E) :
    (List.ofFn f).sum ≤ n * E := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ht := ih (fun i => f i.succ) (fun i => h i.succ)
    have hh := h 0
    simp only [List.ofFn_succ, List.sum_cons]
    rw [Nat.succ_mul]
    omega

theorem actualAdmissibleAggregationBound : Targets.ActualAdmissibleAggregationBound := by
  intro Γ p m E xs hx
  have h := (actualAdmissibleSumSyntax Γ (m + 1) (p.shape .positiveAbstraction m) xs).2.2
  rw [List.map_ofFn] at h
  simp only [Function.comp_def] at h
  have hs := sum_bound (m + 1) E (fun i => ordinalLiteralNodes (xs i)) hx
  omega

private theorem collect_success {α : Type} (n : Nat) (f : Fin n → Option α)
    (v : Fin n → α) (hv : collect n f = some v) : ∀ i, f i = some (v i) := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    have he : ∃ a, f 0 = some a ∧ ∃ w,
        collect n (fun i => f i.succ) = some w ∧ Fin.cases a w = v := by
      simpa only [collect, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hv
    obtain ⟨a, ha, w, hw, rfl⟩ := he
    intro i
    exact Fin.cases ha (ih _ w hw) i

private theorem vectorAt_bound {Γ : List Ty} {m A : Nat} (f : OrdinalVector Γ m)
    (hf : ∀ i, ordinalLiteralNodes (f i) ≤ A) :
    ∀ i, ordinalLiteralNodes (ordinalVectorAt f i) ≤ A := by
  intro i
  have hp := nodes_pos (f 0)
  have h0 := hf 0
  unfold ordinalVectorAt
  split
  · exact hf _
  · simp only [ordinalLiteralNodes]
    omega

private theorem positive_box_bound {Γ : List Ty} (n A B : Nat)
    (f g : Nat → OrdinalExpression Γ)
    (hf : ∀ i, ordinalLiteralNodes (f i) ≤ A)
    (hg : ∀ i, ordinalLiteralNodes (g i) ≤ B) (i : Nat) :
    ordinalLiteralNodes (ordinalBoxPositive n f g i) ≤ A + (n + 1 - i) * (A + B + 2) := by
  rw [ordinalBoxPositive]
  split
  · rename_i hin
    have ih := positive_box_bound n A B f g hf hg (i + 1)
    have hi : n + 1 - i = (n + 1 - (i + 1)) + 1 := by omega
    simp only [ordinalLiteralNodes]
    rw [hi, Nat.add_mul, Nat.one_mul]
    have hfi := hf i
    have hgi := hg i
    omega
  · have hfi := hf i
    omega
termination_by n + 1 - i
decreasing_by omega

private theorem boxTail_bound {Γ : List Ty} (p : Policy) (n A B : Nat)
    (f g : OrdinalExpression Γ) (hf : ordinalLiteralNodes f ≤ A)
    (hg : ordinalLiteralNodes g ≤ B) :
    ordinalLiteralNodes (boxTail p n f g) ≤ A + B + 2 * n + 2 := by
  unfold boxTail
  split
  · simp only [ordinalLiteralNodes]
    omega
  · rename_i hn
    have hnum := actualAdmissibleRepeatExpansion Γ p .numeral n (by omega) (.one)
    change ordinalLiteralNodes (numeral p n) + 1 = n * (1 + 1) at hnum
    have h := (actualAdmissibleSumSyntax Γ 3 (p.shape .optionalBoxTail 2)
      (fun i => if i.val = 0 then f else if i.val = 1 then g else numeral p n)).2.2
    change ordinalLiteralNodes (AdmissiblePartial.three p .optionalBoxTail f g (numeral p n)) + 1 =
      ordinalLiteralNodes f + (ordinalLiteralNodes g + (ordinalLiteralNodes (numeral p n) + 0)) + 3 at h
    omega

theorem actualAdmissibleBoxBound : Targets.ActualAdmissibleBoxBound := by
  intro Γ m n A B p f g hf hg j
  have hb := positive_box_bound n A B (ordinalVectorAt f) (ordinalVectorAt g)
    (vectorAt_bound f hf) (vectorAt_bound g hg)
  unfold box
  split
  · have h1 := hb 1
    have htail := boxTail_bound p n A B (f 0) (g 0) (hf 0) (hg 0)
    simp only [ordinalLiteralNodes]
    unfold boxBound
    have hh : n + 1 - 1 ≤ n + 1 := by omega
    have hm := Nat.mul_le_mul_right (A + B + 2) hh
    nlinarith
  · have hj := hb j.val
    have hh : n + 1 - j.val ≤ n + 1 := Nat.sub_le _ _
    have hm := Nat.mul_le_mul_right (A + B + 2) hh
    unfold boxBound
    nlinarith

theorem actualAdmissibleAbstractionBound : Targets.ActualAdmissibleAbstractionBound := by
  intro Γ σ m N p h hn v hv
  let factor := 2 ^ (σ.level + 1) * ((List.ofFn h).map ordinalPartialSize).sum
  let F := 2 ^ (σ.level + 1) * (m + 1) * 2 ^ N
  let E := 6 * 3 ^ N
  let K := E + N + 3
  have he : ∃ ps : Fin (m + 1) → OrdinalPartialVector Γ σ,
      collect (m + 1) (fun i => AdmissiblePartial.run p i.val (h i)) = some ps ∧
      (fun j : Fin (max (σ.level + 1) m + 1) =>
        let delta : OrdinalExpression Γ :=
          if j.val = 0 then repeated p .scalarRepeat factor (ps 0 0)
          else if hj : j.val < σ.level + 2 then
            expand (p.shape .positiveAbstraction m) (fun i => ps i ⟨j.val, hj⟩)
          else ordinalHeadClosure (h ⟨j.val, by have := j.isLt; omega⟩)
        if hm : j.val < m + 1 then .add delta (ordinalHeadClosure (h ⟨j.val, hm⟩))
        else delta) = v := by
    simpa only [abstraction, bind, pure, Option.bind_eq_some_iff, Option.some.injEq, factor] using hv
  obtain ⟨ps, hps, rfl⟩ := he
  have hp : ∀ i j, ordinalLiteralNodes (ps i j) ≤ E := by
    intro i j
    have hh := actualAdmissiblePartialExpansion Γ σ p i.val (h i) (ps i)
      (collect_success _ _ ps hps i) j
    have hpow := Nat.pow_le_pow_right (n := 3) (by omega) (hn i)
    exact hh.trans (Nat.mul_le_mul_left 6 hpow)
  have hsz : ((List.ofFn h).map ordinalPartialSize).sum ≤ (m + 1) * 2 ^ N := by
    rw [List.map_ofFn]
    apply sum_bound
    intro i
    change ordinalPartialSize (h i) ≤ 2 ^ N
    have hs := actualLiteralPartialSizeBound Γ σ (h i)
    have hpow := Nat.pow_le_pow_right (n := 2) (by omega) (hn i)
    exact hs.1.trans (hs.2.trans ((Nat.sub_le _ _).trans hpow))
  have hF : factor ≤ F := by
    have hh := Nat.mul_le_mul_left (2 ^ (σ.level + 1)) hsz
    simpa only [factor, F, Nat.mul_assoc] using hh
  have hfpos : 0 < factor := by
    have hsum : 0 < ((List.ofFn h).map ordinalPartialSize).sum := by
      rw [List.ofFn_succ, List.map_cons, List.sum_cons]
      have hh := (actualTypedPartialSize Γ σ (h 0)).1
      omega
    exact Nat.mul_pos (Nat.pow_pos (by omega)) hsum
  intro j
  let delta : OrdinalExpression Γ :=
    if j.val = 0 then repeated p .scalarRepeat factor (ps 0 0)
    else if hj : j.val < σ.level + 2 then
      expand (p.shape .positiveAbstraction m) (fun i => ps i ⟨j.val, hj⟩)
    else ordinalHeadClosure (h ⟨j.val, by have := j.isLt; omega⟩)
  have hd : ordinalLiteralNodes delta ≤ (F + m + 1) * K := by
    unfold delta
    split
    · have hc := actualAdmissibleRepeatExpansion Γ p .scalarRepeat factor hfpos (ps 0 0)
      have hm := Nat.mul_le_mul hF (Nat.add_le_add_right (hp 0 0) 1)
      have hbig := Nat.mul_le_mul (by omega : F ≤ F + m + 1) (by dsimp [K]; omega : E + 1 ≤ K)
      omega
    · split
      · have hs := actualAdmissibleAggregationBound Γ p m E
          (fun i => ps i ⟨j.val, by assumption⟩) (fun i => hp i _)
        have hbig := Nat.mul_le_mul (by omega : m + 1 ≤ F + m + 1)
          (by dsimp [K]; omega : E + 1 ≤ K)
        nlinarith
      · rw [nodes_headClosure]
        have hh := hn ⟨j.val, by have := j.isLt; omega⟩
        have hbig := Nat.mul_le_mul_right K (by omega : 1 ≤ F + m + 1)
        dsimp [K] at *
        nlinarith
  change ordinalLiteralNodes (if hm : j.val < m + 1 then
    .add delta (ordinalHeadClosure (h ⟨j.val, hm⟩)) else delta) ≤ _
  change _ ≤ (F + m + 2) * K
  split
  · rename_i hj
    simp only [ordinalLiteralNodes, nodes_headClosure]
    have hh := hn ⟨j.val, hj⟩
    have hk : N + 1 ≤ K := by dsimp [K]; omega
    nlinarith
  · nlinarith

theorem actualAdmissibleSourceBound : Targets.ActualAdmissibleSourceBound := by
  intro Γ τ p t
  induction t with
  | var x => intro v hv; cases hv; intro j; simp [assignment, sourceBound, ordinalLiteralNodes]
  | zeroC => intro v hv; cases hv; intro j; simp [assignment, sourceBound, ordinalLiteralNodes]
  | succC => intro v hv; cases hv; intro j; simp [assignment, sourceBound, ordinalLiteralNodes]
  | caseC σ => intro v hv; cases hv; intro j; simp [assignment, sourceBound, ordinalLiteralNodes]
  | @recC Γ σ =>
    intro v hv
    have he : (fun i => if i.val = 0 then numeral p 2 else if i.val = σ.level + 2 then .omega else .one) = v :=
      Option.some.inj hv
    subst v
    intro j
    dsimp only
    split
    · have hn := actualAdmissibleRepeatExpansion Γ p .numeral 2 (by omega) (.one)
      change ordinalLiteralNodes (numeral p 2) + 1 = 2 * (1 + 1) at hn
      change ordinalLiteralNodes (numeral p 2) ≤ 3
      omega
    · split <;> simp [sourceBound, ordinalLiteralNodes]
  | @app Γ σ τ f a ihf iha =>
    intro v hv
    obtain ⟨vf, hf, gf⟩ := actualAdmissibleAssignmentGenerated Γ (.arrow σ τ) p f
    obtain ⟨va, ha, ga⟩ := actualAdmissibleAssignmentGenerated Γ σ p a
    have he : application p vf va = v := by simpa [assignment, hf, ha] using hv
    subst v
    intro j
    exact actualAdmissibleBoxBound Γ (Ty.arrow σ τ).level σ.level (sourceBound f) (sourceBound a)
      p vf va (ihf vf hf) (iha va ha)
      ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ (Nat.le_max_right _ _))⟩
  | @lam Γ σ τ body ih =>
    intro v hv
    obtain ⟨vb, hb, gb⟩ := actualAdmissibleAssignmentGenerated (σ :: Γ) τ p body
    have ha : abstraction p vb = some v := by
      simp only [assignment, hb, Option.bind_some] at hv
      exact hv
    exact actualAdmissibleAbstractionBound Γ σ τ.level (sourceBound body) p vb (ih vb hb) v ha
  | ranked s args ih => nomatch s

theorem actualAdmissibleUniqueBoundedAssignment : Targets.ActualAdmissibleUniqueBoundedAssignment := by
  intro Γ τ p t
  obtain ⟨v, hv, hg⟩ := actualAdmissibleAssignmentGenerated Γ τ p t
  refine ⟨v, ⟨hv, actualAdmissibleSourceBound Γ τ p t v hv⟩, ?_⟩
  intro w hw
  exact Option.some.inj (hw.1.symm.trans hv)

end LogicLineages.OrdinalComparison.Source.AdmissibleAssignmentBound
