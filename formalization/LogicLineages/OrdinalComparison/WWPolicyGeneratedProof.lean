module
public import LogicLineages.OrdinalComparison.WWPolicyGeneratedTargets
public import LogicLineages.OrdinalComparison.WWGeneratedGradeProof
public import LogicLineages.OrdinalComparison.WWGeneratedSupportProof
public import LogicLineages.OrdinalComparison.WWCanonicalPrimeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.LiteralPolicy
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open GeneratedOrdinalGrade

private theorem free_policy_partial_graded {Γ : List Ty} {σ : Ty} {i : Nat}
    {t : OrdinalExpression (σ :: Γ)} (policy : ActiveSumAssociation) (hg : GeneratedOrdinalGrade (σ :: Γ) i t)
    (hf : ordinalHeadFree t = true) : ∃ v : OrdinalPartialVector Γ σ,
      policyPartial policy i t = some v ∧ ∀ j, GeneratedOrdinalGrade Γ j.val (v j) := by
  refine ⟨ordinalFreePartialVector i t, by rw [policyPartial.eq_def, hf]; rfl, ?_⟩
  intro j
  unfold ordinalFreePartialVector
  split
  · rename_i hij
    rw [← hij]
    exact .add (actualGeneratedGradeHeadClosure Γ σ i t hg) (.one i)
  · exact .one j.val

theorem actualPolicyGeneratedPartial : Targets.ActualPolicyGeneratedPartial := by
  intro Γ σ policy i t h
  induction h with
  | one i => exact free_policy_partial_graded policy (.one i) rfl
  | omega i hi => exact free_policy_partial_graded policy (.omega i hi) rfl
  | var v k =>
    cases v with
    | here =>
      refine ⟨fun _ => .one, ?_, fun j => .one j.val⟩
      rw [policyPartial]
      simp [ordinalHeadFree, ordinalHeadOccurs, ordinalHeadComponentOccurs]
    | there v => exact free_policy_partial_graded policy (.var (.there v) k) rfl
  | @add i f g hf hg ihf ihg =>
    by_cases hfree : ordinalHeadFree (.add f g) = true
    · exact free_policy_partial_graded policy (.add hf hg) hfree
    · obtain ⟨pf, hpf, gpf⟩ := ihf
      obtain ⟨pg, hpg, gpg⟩ := ihg
      refine ⟨fun j => sum3 policy (pf j) (pg j) .one, ?_, ?_⟩
      · rw [policyPartial, Bool.eq_false_iff.mpr hfree, hpf, hpg]
        rfl
      · intro j
        cases policy with
        | left => exact .add (.add (gpf j) (gpg j)) (.one j.val)
        | right => exact .add (gpf j) (.add (gpg j) (.one j.val))
  | @emul i f g hi hf hg ihf ihg =>
    by_cases hfree : ordinalHeadFree (.emul f g) = true
    · exact free_policy_partial_graded policy (.emul hi hf hg) hfree
    · obtain ⟨pf, hpf, gpf⟩ := ihf
      obtain ⟨pg, hpg, gpg⟩ := ihg
      refine ⟨fun j => .add (.add (.add (pf j) (pf j)) (pg j)) .one, ?_, ?_⟩
      · rw [policyPartial, Bool.eq_false_iff.mpr hfree, if_pos hi,
          hpf, hpg]
        rfl
      · intro j
        exact .add (.add (.add (gpf j) (gpf j)) (gpg j)) (.one j.val)
  | @collapse f g hf hg ihf ihg =>
    by_cases hfree : ordinalHeadFree (.collapse f g) = true
    · exact free_policy_partial_graded policy (.collapse hf hg) hfree
    · obtain ⟨pf, hpf, gpf⟩ := ihf
      obtain ⟨pg, hpg, gpg⟩ := ihg
      refine ⟨fun j => if j.val = 0 then .collapse (ordinalHeadClosure f) (pg 0)
        else .add (pf j) (pg j), ?_, ?_⟩
      · rw [policyPartial, Bool.eq_false_iff.mpr hfree, if_pos rfl,
          hpf, hpg]
        rfl
      · intro j
        dsimp only
        split
        · rename_i hj
          rw [hj]
          exact .collapse (actualGeneratedGradeHeadClosure Γ σ 1 f hf) (gpg 0)
        · exact .add (gpf j) (gpg j)


private theorem foldl_add_grade {Γ : List Ty} {i : Nat} (xs : List (OrdinalExpression Γ))
    (hx : ∀ x ∈ xs, GeneratedOrdinalGrade Γ i x) (a : OrdinalExpression Γ)
    (ha : GeneratedOrdinalGrade Γ i a) :
    GeneratedOrdinalGrade Γ i (xs.foldl (fun u v => .add u v) a) := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    exact ih (fun z hz => hx z (by simp [hz])) (.add a x) (.add ha (hx x (by simp)))

private theorem repeat_grade {Γ : List Ty} {i : Nat} (k : Nat) (hk : 0 < k)
    (t : OrdinalExpression Γ) (ht : GeneratedOrdinalGrade Γ i t) :
    GeneratedOrdinalGrade Γ i (literalRepeat k t) := by
  cases k with
  | zero => omega
  | succ k =>
    apply foldl_add_grade
    · intro x hx
      have : x = t := (List.mem_replicate.mp hx).2
      simpa [this] using ht
    · exact ht

private theorem partial_list {Γ : List Ty} {σ : Ty} {m : Nat}
    (policy : ActiveSumAssociation) (h : OrdinalVector (σ :: Γ) m)
    (hg : ∀ i, GeneratedOrdinalGrade (σ :: Γ) i.val (h i))
    (is : List (Fin (m + 1))) :
    ∃ ps : List (OrdinalPartialVector Γ σ),
      is.mapM (fun i => policyPartial policy i.val (h i)) = some ps ∧
      ps.length = is.length ∧
      ∀ p ∈ ps, ∀ j, GeneratedOrdinalGrade Γ j.val (p j) := by
  induction is with
  | nil => exact ⟨[], rfl, rfl, by simp⟩
  | cons i is ih =>
    obtain ⟨p, hp, gp⟩ := actualPolicyGeneratedPartial Γ σ policy i.val (h i) (hg i)
    obtain ⟨ps, hps, hlen, gps⟩ := ih
    refine ⟨p :: ps, ?_, by simp [hlen], ?_⟩
    · simp [hp, hps]
    · intro q hq j
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact gp j
      · exact gps q hq j

private theorem partial_fold_grade {Γ : List Ty} {σ : Ty}
    (ps : List (OrdinalPartialVector Γ σ))
    (hg : ∀ p ∈ ps, ∀ j, GeneratedOrdinalGrade Γ j.val (p j))
    (j : Fin (σ.level + 2)) (a : OrdinalExpression Γ)
    (ha : GeneratedOrdinalGrade Γ j.val a) :
    GeneratedOrdinalGrade Γ j.val (ps.foldl (fun a p => .add a (p j)) a) := by
  induction ps generalizing a with
  | nil => exact ha
  | cons p ps ih =>
    exact ih (fun q hq => hg q (by simp [hq])) (.add a (p j))
      (.add ha (hg p (by simp) j))

theorem actualPolicyGeneratedAbstraction : Targets.ActualPolicyGeneratedAbstraction := by
  intro Γ σ m policy h hg
  obtain ⟨ps, hps, hlen, gps⟩ := partial_list policy h hg (List.finRange (m + 1))
  have hlen' : ps.length = m + 1 := by simpa using hlen
  cases ps with
  | nil => simp at hlen'
  | cons p0 rest =>
    let factor := 2 ^ (σ.level + 1) *
      ((List.finRange (m + 1)).map (fun i => ordinalPartialSize (h i))).sum
    have hsum : 0 < ((List.finRange (m + 1)).map (fun i => ordinalPartialSize (h i))).sum := by
      rw [List.finRange_succ, List.map_cons, List.sum_cons]
      have := (actualTypedPartialSize Γ σ (h 0)).1
      omega
    have hfactor : 0 < factor := Nat.mul_pos (Nat.pow_pos (by omega)) hsum
    let v : OrdinalVector Γ (max (σ.level + 1) m) := fun j =>
      let delta : OrdinalExpression Γ :=
        if j.val = 0 then literalRepeat factor (p0 0)
        else if hj : j.val < σ.level + 2 then
          rest.foldl (fun a p => .add a (p ⟨j.val, hj⟩)) (p0 ⟨j.val, hj⟩)
        else if hm : j.val < m + 1 then ordinalHeadClosure (h ⟨j.val, hm⟩)
        else .zero
      if hm : j.val < m + 1 then .add delta (ordinalHeadClosure (h ⟨j.val, hm⟩))
      else delta
    refine ⟨v, ?_, ?_⟩
    · simp only [abstraction, hps, Option.bind_some]
      rfl
    · intro j
      have hd : GeneratedOrdinalGrade Γ j.val
          (if j.val = 0 then literalRepeat factor (p0 0)
           else if hj : j.val < σ.level + 2 then
             rest.foldl (fun a p => .add a (p ⟨j.val, hj⟩)) (p0 ⟨j.val, hj⟩)
           else if hm : j.val < m + 1 then ordinalHeadClosure (h ⟨j.val, hm⟩)
           else .zero) := by
        split
        · rename_i hj
          rw [hj]
          exact repeat_grade factor hfactor _ (gps p0 (by simp) 0)
        · split
          · rename_i hj
            exact partial_fold_grade rest (fun p hp => gps p (by simp [hp]))
              ⟨j.val, hj⟩ _ (gps p0 (by simp) ⟨j.val, hj⟩)
          · split
            · rename_i hm
              exact actualGeneratedGradeHeadClosure Γ σ j.val _ (hg ⟨j.val, hm⟩)
            · have := j.isLt
              omega
      by_cases hm : j.val < m + 1
      · simpa only [v, dif_pos hm] using
          (GeneratedOrdinalGrade.add hd
            (actualGeneratedGradeHeadClosure Γ σ j.val _ (hg ⟨j.val, hm⟩)))
      · simpa only [v, dif_neg hm] using hd

theorem actualPolicyGeneratedAssignment : Targets.ActualPolicyGeneratedAssignment := by
  intro Γ τ policy t
  induction t with
  | var v => exact ⟨_, rfl, fun i => .var v i⟩
  | zeroC => exact ⟨_, rfl, fun i => .one i.val⟩
  | succC => exact ⟨_, rfl, fun i => .one i.val⟩
  | caseC σ => exact ⟨_, rfl, fun i => .one i.val⟩
  | recC σ =>
    refine ⟨_, rfl, ?_⟩
    intro i
    split
    · exact .add (.one i.val) (.one i.val)
    · split
      · exact .omega i.val (by omega)
      · exact .one i.val
  | @app Γ σ τ f a ihf iha =>
    obtain ⟨vf, hf, gf⟩ := ihf
    obtain ⟨va, ha, ga⟩ := iha
    refine ⟨ordinalCanonicalApplication vf va, ?_, ?_⟩
    · simp [assignment, hf, ha]
    · intro i
      exact ((actualCanonicalTypedApplication Γ σ τ).2.2 vf va gf ga i).1
  | @lam Γ σ τ body ih =>
    obtain ⟨vb, hb, gb⟩ := ih
    obtain ⟨v, hv, gv⟩ := actualPolicyGeneratedAbstraction Γ σ τ.level policy vb gb
    refine ⟨v, ?_, gv⟩
    simp [assignment, hb, hv]
    rfl
  | ranked s args ih => nomatch s

theorem actualPolicyGroundPositiveClosed : Targets.ActualPolicyGroundPositiveClosed := by
  intro Γ hΓ τ policy t
  obtain ⟨v, hv, gv⟩ := actualPolicyGeneratedAssignment Γ τ policy t
  exact ⟨v, hv, fun j hj => actualGeneratedGroundPositiveClosed Γ hΓ j.val (v j) hj (gv j)⟩

end LogicLineages.OrdinalComparison.Source.LiteralPolicy
