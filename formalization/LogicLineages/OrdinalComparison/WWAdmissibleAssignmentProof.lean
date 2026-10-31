module
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentTargets
public import LogicLineages.OrdinalComparison.WWAdmissiblePartialProof
public import LogicLineages.OrdinalComparison.WWGeneratedSupportProof
public import LogicLineages.OrdinalComparison.WWCanonicalBoxProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AdmissibleAssignment
open AdmissibleSum

private theorem collect_property {α : Type} (P : α → Prop) (n : Nat)
    (f : Fin n → Option α) (hf : ∀ i, ∃ a, f i = some a ∧ P a) :
    ∃ v, collect n f = some v ∧ ∀ i, P (v i) := by
  induction n with
  | zero => exact ⟨Fin.elim0, rfl, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨a, ha, ga⟩ := hf 0
    obtain ⟨v, hv, gv⟩ := ih (fun i => f i.succ) (fun i => hf i.succ)
    refine ⟨Fin.cases a v, ?_, ?_⟩
    · simp [collect, ha, hv]
    · intro i
      exact Fin.cases ga gv i

private theorem repeated_generated {Γ : List Ty} {i : Nat} (p : Policy)
    (site : MacroSite) (k : Nat) (hk : 0 < k) (t : OrdinalExpression Γ)
    (ht : GeneratedOrdinalGrade Γ i t) :
    GeneratedOrdinalGrade Γ i (repeated p site k t) := by
  cases k with
  | zero => omega
  | succ k => exact expand_generated _ _ (fun _ => ht)

private theorem numeral_generated {Γ : List Ty} (p : Policy) (i n : Nat) (hn : 0 < n) :
    GeneratedOrdinalGrade Γ i (numeral p n) :=
  repeated_generated p .numeral n hn .one (.one i)

private theorem boxTail_generated {Γ : List Ty} (p : Policy) (n : Nat)
    (f g : OrdinalExpression Γ) (hf : GeneratedOrdinalGrade Γ 0 f)
    (hg : GeneratedOrdinalGrade Γ 0 g) : GeneratedOrdinalGrade Γ 0 (boxTail p n f g) := by
  unfold boxTail
  split
  · exact .add hf hg
  · rename_i hn
    apply expand_generated
    intro j
    split
    · exact hf
    · split
      · exact hg
      · exact numeral_generated p 0 n (by omega)

private theorem box_generated {Γ : List Ty} {m n : Nat} (p : Policy) (hnm : n < m)
    (f : OrdinalVector Γ m) (g : OrdinalVector Γ n)
    (hf : ∀ i, GeneratedOrdinalGrade Γ i.val (f i))
    (hg : ∀ i, GeneratedOrdinalGrade Γ i.val (g i)) :
    ∀ i, GeneratedOrdinalGrade Γ i.val (box p f g i) := by
  intro i
  have hold := actualCanonicalBoxGeneratedGrade Γ m n hnm f g hf hg
  by_cases hi : i.val = 0
  · have hi' : i = 0 := Fin.ext hi
    subst i
    have h1 := hold ⟨1, by omega⟩
    change GeneratedOrdinalGrade Γ 1
      (if 1 = 0 then _ else ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) 1) at h1
    simp only [Nat.one_ne_zero, if_false] at h1
    exact .collapse h1 (boxTail_generated p n (f 0) (g 0) (hf 0) (hg 0))
  · simpa only [box, ordinalCanonicalBox, hi, if_false] using hold i

private theorem application_generated {Γ : List Ty} {σ τ : Ty} (p : Policy)
    (f : OrdinalVector Γ (Ty.arrow σ τ).level) (g : OrdinalVector Γ σ.level)
    (hf : ∀ i, GeneratedOrdinalGrade Γ i.val (f i))
    (hg : ∀ i, GeneratedOrdinalGrade Γ i.val (g i)) :
    ∀ i, GeneratedOrdinalGrade Γ i.val (application p f g i) := by
  intro i
  exact box_generated p (by simp only [Ty.level]; omega) f g hf hg
    ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ (Nat.le_max_right _ _))⟩

theorem actualAdmissibleAbstractionGenerated : Targets.ActualAdmissibleAbstractionGenerated := by
  intro Γ σ m p h hg
  obtain ⟨ps, hps, gps⟩ := collect_property
    (fun v : OrdinalPartialVector Γ σ => ∀ j, GeneratedOrdinalGrade Γ j.val (v j))
    (m + 1) (fun i => AdmissiblePartial.run p i.val (h i))
    (fun i => AdmissiblePartial.actualAdmissiblePartialGenerated Γ σ p i.val (h i) (hg i))
  let factor := 2 ^ (σ.level + 1) * ((List.ofFn h).map ordinalPartialSize).sum
  have hsum : 0 < ((List.ofFn h).map ordinalPartialSize).sum := by
    rw [List.ofFn_succ, List.map_cons, List.sum_cons]
    have := (actualTypedPartialSize Γ σ (h 0)).1
    omega
  have hfactor : 0 < factor := Nat.mul_pos (Nat.pow_pos (by omega)) hsum
  let v : OrdinalVector Γ (max (σ.level + 1) m) := fun j =>
    let delta : OrdinalExpression Γ :=
      if j.val = 0 then repeated p .scalarRepeat factor (ps 0 0)
      else if hj : j.val < σ.level + 2 then
        expand (p.shape .positiveAbstraction m) (fun i => ps i ⟨j.val, hj⟩)
      else ordinalHeadClosure (h ⟨j.val, by have := j.isLt; omega⟩)
    if hm : j.val < m + 1 then .add delta (ordinalHeadClosure (h ⟨j.val, hm⟩))
    else delta
  refine ⟨v, ?_, ?_⟩
  · simp only [abstraction, hps, Option.bind_some]
    rfl
  · intro j
    have hd : GeneratedOrdinalGrade Γ j.val
        (if j.val = 0 then repeated p .scalarRepeat factor (ps 0 0)
         else if hj : j.val < σ.level + 2 then
           expand (p.shape .positiveAbstraction m) (fun i => ps i ⟨j.val, hj⟩)
         else ordinalHeadClosure (h ⟨j.val, by have := j.isLt; omega⟩)) := by
      split
      · rename_i hj
        rw [hj]
        exact repeated_generated p .scalarRepeat factor hfactor _ (gps 0 0)
      · split
        · rename_i hj
          exact expand_generated _ _ (fun i => gps i ⟨j.val, hj⟩)
        · exact actualGeneratedGradeHeadClosure Γ σ j.val _
            (hg ⟨j.val, by have := j.isLt; omega⟩)
    by_cases hm : j.val < m + 1
    · simpa only [v, dif_pos hm] using
        (GeneratedOrdinalGrade.add hd
          (actualGeneratedGradeHeadClosure Γ σ j.val _ (hg ⟨j.val, hm⟩)))
    · simpa only [v, dif_neg hm] using hd

theorem actualAdmissibleAssignmentGenerated : Targets.ActualAdmissibleAssignmentGenerated := by
  intro Γ τ p t
  induction t with
  | var v => exact ⟨_, rfl, fun i => .var v i⟩
  | zeroC => exact ⟨_, rfl, fun i => .one i.val⟩
  | succC => exact ⟨_, rfl, fun i => .one i.val⟩
  | caseC σ => exact ⟨_, rfl, fun i => .one i.val⟩
  | recC σ =>
    refine ⟨_, rfl, ?_⟩
    intro i
    split
    · exact numeral_generated p i.val 2 (by omega)
    · split
      · exact .omega i.val (by omega)
      · exact .one i.val
  | @app Γ σ τ f a ihf iha =>
    obtain ⟨vf, hf, gf⟩ := ihf
    obtain ⟨va, ha, ga⟩ := iha
    refine ⟨application p vf va, ?_, application_generated p vf va gf ga⟩
    simp [assignment, hf, ha]
  | @lam Γ σ τ body ih =>
    obtain ⟨vb, hb, gb⟩ := ih
    obtain ⟨v, hv, gv⟩ := actualAdmissibleAbstractionGenerated Γ σ τ.level p vb gb
    refine ⟨v, ?_, gv⟩
    simp [assignment, hb, hv]
    rfl
  | ranked s args ih => nomatch s

theorem actualAdmissibleAssignmentPositiveClosed : Targets.ActualAdmissibleAssignmentPositiveClosed := by
  intro Γ hΓ τ p t
  obtain ⟨v, hv, gv⟩ := actualAdmissibleAssignmentGenerated Γ τ p t
  exact ⟨v, hv, fun j hj => actualGeneratedGroundPositiveClosed Γ hΓ j.val (v j) hj (gv j)⟩

end LogicLineages.OrdinalComparison.Source.AdmissibleAssignment
