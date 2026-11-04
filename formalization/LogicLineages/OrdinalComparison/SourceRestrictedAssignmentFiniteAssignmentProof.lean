module
public import LogicLineages.OrdinalComparison.SourceRestrictedAssignmentFiniteTargets
public import LogicLineages.OrdinalComparison.WWOriginalAssignmentNormProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceRestrictedAssignmentFinite.Proof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open AdmissibleSum AdmissibleAssignment

private theorem closure_free {Γ σ} (t : OrdinalExpression (σ :: Γ))
    (ht : OmegaFree t) : OmegaFree (ordinalHeadClosure t) := by
  induction t with
  | var c =>
    rcases c with ⟨τ, x, j⟩
    cases x <;> trivial
  | zero | one => trivial
  | omega => exact ht.elim
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    exact ⟨iha ht.1, ihb ht.2⟩

private theorem expand_free {Γ n} (s : Shape n) (xs : Fin n → OrdinalExpression Γ)
    (h : ∀ i, OmegaFree (xs i)) : OmegaFree (expand s xs) := by
  induction s with
  | leaf => exact h 0
  | join a b iha ihb => exact ⟨iha _ (fun i => h _), ihb _ (fun i => h _)⟩

private theorem three_free {Γ} (p : Policy) (site : MacroSite)
    (a b c : OrdinalExpression Γ) (ha : OmegaFree a) (hb : OmegaFree b)
    (hc : OmegaFree c) : OmegaFree (AdmissiblePartial.three p site a b c) := by
  apply expand_free
  intro i
  split_ifs <;> assumption

private theorem twice_free {Γ} (p : Policy) (a : OrdinalExpression Γ)
    (ha : OmegaFree a) : OmegaFree (AdmissiblePartial.twice p a) :=
  expand_free _ _ (fun _ => ha)

private theorem repeated_free {Γ} (p : Policy) (site : MacroSite) (n : Nat)
    (a : OrdinalExpression Γ) (ha : OmegaFree a) : OmegaFree (repeated p site n a) := by
  cases n with
  | zero => trivial
  | succ n => exact expand_free _ _ (fun _ => ha)

private theorem free_partial_free {Γ σ} (i : Nat) (t : OrdinalExpression (σ :: Γ))
    (ht : OmegaFree t) : ∀ j, OmegaFree (ordinalFreePartialVector i t j) := by
  intro j
  unfold ordinalFreePartialVector
  split_ifs
  · exact ⟨closure_free t ht, trivial⟩
  · trivial

private theorem run_free_case {Γ σ} (p : Policy) (i : Nat)
    (t : OrdinalExpression (σ :: Γ)) (ht : OmegaFree t)
    (hf : ordinalHeadFree t = true) (v : OrdinalPartialVector Γ σ)
    (hv : AdmissiblePartial.run p i t = some v) : ∀ j, OmegaFree (v j) := by
  rw [AdmissiblePartial.run.eq_def, hf] at hv
  simp only [↓reduceIte, Option.some.injEq] at hv
  subst v
  exact free_partial_free i t ht

private theorem run_free {Γ σ} (p : Policy) (t : OrdinalExpression (σ :: Γ))
    (ht : OmegaFree t) (i : Nat) (v : OrdinalPartialVector Γ σ)
    (hv : AdmissiblePartial.run p i t = some v) : ∀ j, OmegaFree (v j) := by
  induction t generalizing i v with
  | var c =>
    by_cases hf : ordinalHeadFree (.var c) = true
    · exact run_free_case p i _ ht hf v hv
    · rcases c with ⟨τ, x, k⟩
      rw [AdmissiblePartial.run.eq_def] at hv
      simp only [hf, Bool.false_eq_true, ↓reduceIte] at hv
      split_ifs at hv with hi
      · cases hv; intro j; trivial
  | zero => exact run_free_case p i _ ht rfl v hv
  | one => exact run_free_case p i _ ht rfl v hv
  | omega => exact ht.elim
  | add a b iha ihb =>
    by_cases hf : ordinalHeadFree (.add a b) = true
    · exact run_free_case p i _ ht hf v hv
    · rw [AdmissiblePartial.run.eq_def] at hv
      simp only [hf, Bool.false_eq_true, ↓reduceIte] at hv
      cases ha : AdmissiblePartial.run p i a with
      | none => simp [ha] at hv
      | some va =>
        cases hb : AdmissiblePartial.run p i b with
        | none => simp [ha, hb] at hv
        | some vb =>
          simp only [ha, hb, bind, pure, Option.bind_some, Option.some.injEq] at hv
          subst v
          intro j
          exact three_free p .activeAdd _ _ .one (iha ht.1 i va ha j) (ihb ht.2 i vb hb j) trivial
  | emul a b iha ihb =>
    by_cases hf : ordinalHeadFree (.emul a b) = true
    · exact run_free_case p i _ ht hf v hv
    · rw [AdmissiblePartial.run.eq_def] at hv
      simp only [hf, Bool.false_eq_true, ↓reduceIte] at hv
      split_ifs at hv with hi
      · cases ha : AdmissiblePartial.run p (i + 1) a with
        | none => simp [ha] at hv
        | some va =>
          cases hb : AdmissiblePartial.run p i b with
          | none => simp [ha, hb] at hv
          | some vb =>
            simp only [ha, hb, bind, pure, Option.bind_some, Option.some.injEq] at hv
            subst v
            intro j
            exact three_free p .activeExp _ _ .one (twice_free p _ (iha ht.1 (i + 1) va ha j))
              (ihb ht.2 i vb hb j) trivial
  | collapse a b iha ihb =>
    by_cases hf : ordinalHeadFree (.collapse a b) = true
    · exact run_free_case p i _ ht hf v hv
    · rw [AdmissiblePartial.run.eq_def] at hv
      simp only [hf, Bool.false_eq_true, ↓reduceIte] at hv
      split_ifs at hv with hi
      · cases ha : AdmissiblePartial.run p 1 a with
        | none => simp [ha] at hv
        | some va =>
          cases hb : AdmissiblePartial.run p 0 b with
          | none => simp [ha, hb] at hv
          | some vb =>
            simp only [ha, hb, bind, pure, Option.bind_some, Option.some.injEq] at hv
            subst v
            intro j
            change OmegaFree (if j.val = 0 then .collapse (ordinalHeadClosure a) (vb 0)
              else .add (va j) (vb j))
            split_ifs
            · exact ⟨closure_free a ht.1, ihb ht.2 0 vb hb 0⟩
            · exact ⟨iha ht.1 1 va ha j, ihb ht.2 0 vb hb j⟩

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

private theorem abstraction_free {Γ σ m} (p : Policy) (h : OrdinalVector (σ :: Γ) m)
    (hh : ∀ j, OmegaFree (h j)) (v : OrdinalVector Γ (max (σ.level + 1) m))
    (hv : abstraction p h = some v) : ∀ j, OmegaFree (v j) := by
  unfold abstraction at hv
  cases hps : collect (m + 1) (fun i => AdmissiblePartial.run p i.val (h i)) with
  | none => simp [hps] at hv
  | some ps =>
    simp only [hps, bind, pure, Option.bind_some, Option.some.injEq] at hv
    have hs : ∀ i j, OmegaFree (ps i j) := fun i =>
      run_free p (h i) (hh i) i.val (ps i) (collect_success _ _ ps hps i)
    subst v
    intro j
    dsimp only
    split_ifs <;>
      first
      | exact ⟨repeated_free p _ _ _ (hs 0 0), closure_free _ (hh _)⟩
      | exact ⟨expand_free _ _ (fun i => hs i _), closure_free _ (hh _)⟩
      | exact ⟨closure_free _ (hh _), closure_free _ (hh _)⟩
      | exact repeated_free p _ _ _ (hs 0 0)
      | exact expand_free _ _ (fun i => hs i _)
      | exact closure_free _ (hh _)

private theorem vector_at_free {Γ m} (v : OrdinalVector Γ m)
    (hv : ∀ j, OmegaFree (v j)) (i : Nat) : OmegaFree (ordinalVectorAt v i) := by
  unfold ordinalVectorAt
  split_ifs
  · exact hv _
  · trivial

private theorem positive_free {Γ} (n : Nat) (f g : Nat → OrdinalExpression Γ)
    (hf : ∀ i, OmegaFree (f i)) (hg : ∀ i, OmegaFree (g i)) (i : Nat) :
    OmegaFree (ordinalBoxPositive n f g i) := by
  rw [ordinalBoxPositive.eq_def]
  split_ifs with hi
  · exact ⟨positive_free n f g hf hg (i + 1), hf i, hg i⟩
  · exact hf i
termination_by n + 1 - i
decreasing_by omega

private theorem application_free {Γ σ τ} (p : Policy)
    (f : OrdinalVector Γ (Ty.arrow σ τ).level) (g : OrdinalVector Γ σ.level)
    (hf : ∀ j, OmegaFree (f j)) (hg : ∀ j, OmegaFree (g j)) :
    ∀ j, OmegaFree (application p f g j) := by
  intro j
  unfold application box
  split_ifs
  · refine ⟨positive_free _ _ _ (vector_at_free f hf) (vector_at_free g hg) _, ?_⟩
    unfold boxTail
    split_ifs
    · exact ⟨hf 0, hg 0⟩
    · exact three_free p _ _ _ _ (hf 0) (hg 0) (repeated_free p _ _ _ trivial)
  · exact positive_free _ _ _ (vector_at_free f hf) (vector_at_free g hg) _

private theorem assignment_free {Γ τ} (p : Policy) (t : OriginalTerm Γ τ)
    (ht : SourceGroundBinderFragment.Fragment t) (v : OrdinalVector Γ τ.level)
    (hv : assignment p t = some v) : ∀ j, OmegaFree (v j) := by
  induction t with
  | var x => cases hv; intro j; trivial
  | zeroC => cases hv; intro j; trivial
  | succC => cases hv; intro j; trivial
  | caseC σ => exact ht.elim
  | recC σ => exact ht.elim
  | app f a ihf iha =>
    cases hf : assignment p f with
    | none => simp [assignment, hf] at hv
    | some vf =>
      cases ha : assignment p a with
      | none => simp [assignment, hf, ha] at hv
      | some va =>
        simp only [assignment, hf, ha, bind, pure, Option.bind_some, Option.some.injEq] at hv
        subst v
        exact application_free p vf va (ihf ht.1 vf hf) (iha ht.2 va ha)
  | lam body ih =>
    cases hb : assignment p body with
    | none => simp [assignment, hb] at hv
    | some vb =>
      simp only [assignment, hb, bind, Option.bind_some] at hv
      exact abstraction_free p vb (ih ht.2 vb hb) v hv
  | ranked s args ih => nomatch s

theorem actualAssignment : Targets.ActualAssignment := by
  intro Γ τ t _ ht
  obtain ⟨v, hv, _, _⟩ := OriginalDomain.originalSourceAssignmentBounded
    Γ τ OrdinalSyntax.defaultPolicy t
  exact ⟨v, hv, assignment_free OrdinalSyntax.defaultPolicy t ht v hv⟩

end LogicLineages.OrdinalComparison.Source.SourceRestrictedAssignmentFinite.Proof
