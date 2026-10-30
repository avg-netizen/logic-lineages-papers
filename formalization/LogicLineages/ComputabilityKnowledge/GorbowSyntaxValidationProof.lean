module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowSyntaxValidation
public import LogicLineages.ComputabilityKnowledge.GorbowTermPrefixCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaPrefixCodeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSyntaxValidationProof
open GorbowSyntax GorbowSyntaxValidation

private theorem advance {tasks whole} (h : StackMeaning tasks whole) :
    ∀ x raw, whole = x :: raw → ∃ next, step (some tasks) x = some next ∧ StackMeaning next raw := by
  cases h with
  | nil => intro x raw he; cases he
  | index i hi ht =>
      intro x raw he
      cases he
      exact ⟨_, by simp [step, expand, hi], ht⟩
  | @term n tasks tail t ht =>
      cases t with
      | var i =>
          intro x raw he
          simp only [GorbowTermPrefixCode.encode, List.cons_append, List.nil_append, List.cons.injEq] at he
          rcases he with ⟨rfl, rfl⟩
          exact ⟨_, by simp [step, expand], StackMeaning.index i.val i.isLt ht⟩
      | zero  =>
          intro x raw he
          simp only [GorbowTermPrefixCode.encode, List.cons_append, List.nil_append, List.cons.injEq] at he
          rcases he with ⟨rfl, rfl⟩
          exact ⟨_, by simp [step, expand], ht⟩
      | succ t =>
          intro x raw he
          simp only [GorbowTermPrefixCode.encode, List.cons_append, List.nil_append, List.cons.injEq] at he
          rcases he with ⟨rfl, rfl⟩
          exact ⟨_, by simp [step, expand], StackMeaning.term t ht⟩
      | add t u =>
          intro x raw he
          simp only [GorbowTermPrefixCode.encode, List.cons_append, List.nil_append, List.cons.injEq] at he
          rcases he with ⟨rfl, rfl⟩
          refine ⟨(0,n)::(0,n)::tasks, ?_, ?_⟩
          · simp [step, expand]
          · simpa only [List.append_assoc] using StackMeaning.term t (StackMeaning.term u ht)
      | mul t u =>
          intro x raw he
          simp only [GorbowTermPrefixCode.encode, List.cons_append, List.nil_append, List.cons.injEq] at he
          rcases he with ⟨rfl, rfl⟩
          refine ⟨(0,n)::(0,n)::tasks, ?_, ?_⟩
          · simp [step, expand]
          · simpa only [List.append_assoc] using StackMeaning.term t (StackMeaning.term u ht)
      | universalFunction t =>
          intro x raw he
          simp only [GorbowTermPrefixCode.encode, List.cons_append, List.nil_append, List.cons.injEq] at he
          rcases he with ⟨rfl, rfl⟩
          exact ⟨_, by simp [step, expand], StackMeaning.term t ht⟩
  | @formula n tasks tail φ ht =>
      cases φ with
      | equal t u =>
          intro x raw he
          simp only [GorbowFormulaPrefixCode.encode, List.cons_append, List.cons.injEq] at he
          rcases he with ⟨rfl, rfl⟩
          refine ⟨(0,n)::(0,n)::tasks, ?_, ?_⟩
          · simp [step, expand]
          · simpa only [List.append_assoc] using StackMeaning.term t (StackMeaning.term u ht)
      | universalRelation t =>
          intro x raw he
          simp only [GorbowFormulaPrefixCode.encode, List.cons_append, List.cons.injEq] at he
          rcases he with ⟨rfl, rfl⟩
          exact ⟨_, by simp [step, expand], StackMeaning.term t ht⟩
      | agent t =>
          intro x raw he
          simp only [GorbowFormulaPrefixCode.encode, List.cons_append, List.cons.injEq] at he
          rcases he with ⟨rfl, rfl⟩
          exact ⟨_, by simp [step, expand], StackMeaning.term t ht⟩
      | knowledgeAll t =>
          intro x raw he
          simp only [GorbowFormulaPrefixCode.encode, List.cons_append, List.cons.injEq] at he
          rcases he with ⟨rfl, rfl⟩
          exact ⟨_, by simp [step, expand], StackMeaning.term t ht⟩
      | knowledge t u =>
          intro x raw he
          simp only [GorbowFormulaPrefixCode.encode, List.cons_append, List.cons.injEq] at he
          rcases he with ⟨rfl, rfl⟩
          refine ⟨(0,n)::(0,n)::tasks, ?_, ?_⟩
          · simp [step, expand]
          · simpa only [List.append_assoc] using StackMeaning.term t (StackMeaning.term u ht)
      | truth t =>
          intro x raw he
          simp only [GorbowFormulaPrefixCode.encode, List.cons_append, List.cons.injEq] at he
          rcases he with ⟨rfl, rfl⟩
          exact ⟨_, by simp [step, expand], StackMeaning.term t ht⟩
      | neg φ =>
          intro x raw he
          simp only [GorbowFormulaPrefixCode.encode, List.cons_append, List.cons.injEq] at he
          rcases he with ⟨rfl, rfl⟩
          exact ⟨_, by simp [step, expand], StackMeaning.formula φ ht⟩
      | imp φ ψ =>
          intro x raw he
          simp only [GorbowFormulaPrefixCode.encode, List.cons_append, List.cons.injEq] at he
          rcases he with ⟨rfl, rfl⟩
          refine ⟨(1,n)::(1,n)::tasks, ?_, ?_⟩
          · simp [step, expand]
          · simpa only [List.append_assoc] using StackMeaning.formula φ (StackMeaning.formula ψ ht)
      | conj φ ψ =>
          intro x raw he
          simp only [GorbowFormulaPrefixCode.encode, List.cons_append, List.cons.injEq] at he
          rcases he with ⟨rfl, rfl⟩
          refine ⟨(1,n)::(1,n)::tasks, ?_, ?_⟩
          · simp [step, expand]
          · simpa only [List.append_assoc] using StackMeaning.formula φ (StackMeaning.formula ψ ht)
      | disj φ ψ =>
          intro x raw he
          simp only [GorbowFormulaPrefixCode.encode, List.cons_append, List.cons.injEq] at he
          rcases he with ⟨rfl, rfl⟩
          refine ⟨(1,n)::(1,n)::tasks, ?_, ?_⟩
          · simp [step, expand]
          · simpa only [List.append_assoc] using StackMeaning.formula φ (StackMeaning.formula ψ ht)
      | all φ =>
          intro x raw he
          simp only [GorbowFormulaPrefixCode.encode, List.cons_append, List.cons.injEq] at he
          rcases he with ⟨rfl, rfl⟩
          exact ⟨_, by simp [step, expand], StackMeaning.formula φ ht⟩
      | ex φ =>
          intro x raw he
          simp only [GorbowFormulaPrefixCode.encode, List.cons_append, List.cons.injEq] at he
          rcases he with ⟨rfl, rfl⟩
          exact ⟨_, by simp [step, expand], StackMeaning.formula φ ht⟩

private theorem retreat (tasks : List Task) (x : Nat) (next : List Task) (raw : List Nat)
    (hs : step (some tasks) x = some next) (hm : StackMeaning next raw) :
    StackMeaning tasks (x :: raw) := by
  cases tasks with
  | nil => simp [step] at hs
  | cons task tasks =>
      rcases task with ⟨kind, n⟩
      by_cases hk : kind ≤ 2
      · interval_cases kind
        · by_cases hx : x ≤ 5
          · interval_cases x
            · simp [step, expand] at hs
              subst next
              cases hm with
              | index i hi ht => exact StackMeaning.term (.var ⟨i, hi⟩) ht
            · simp [step, expand] at hs
              subst next
              exact StackMeaning.term .zero hm
            · simp [step, expand] at hs
              subst next
              cases hm with
              | term t ht => exact StackMeaning.term (.succ t) ht
            · simp [step, expand] at hs
              subst next
              cases hm with
              | term t ht =>
                  cases ht with
                  | term u hu => simpa only [GorbowTermPrefixCode.encode, GorbowFormulaPrefixCode.encode, List.cons_append, List.append_assoc] using StackMeaning.term (.add t u) hu
            · simp [step, expand] at hs
              subst next
              cases hm with
              | term t ht =>
                  cases ht with
                  | term u hu => simpa only [GorbowTermPrefixCode.encode, GorbowFormulaPrefixCode.encode, List.cons_append, List.append_assoc] using StackMeaning.term (.mul t u) hu
            · simp [step, expand] at hs
              subst next
              cases hm with
              | term t ht => exact StackMeaning.term (.universalFunction t) ht
          · have hx0 : x ≠ 0 := by omega
            have hx1 : x ≠ 1 := by omega
            have hx2 : x ≠ 2 := by omega
            have hx3 : x ≠ 3 := by omega
            have hx4 : x ≠ 4 := by omega
            have hx5 : x ≠ 5 := by omega
            simp [step, expand, hx0, hx1, hx2, hx3, hx4, hx5] at hs
        · by_cases hx : x ≤ 11
          · interval_cases x
            · simp [step, expand] at hs
              subst next
              cases hm with
              | term t ht =>
                  cases ht with
                  | term u hu => simpa only [GorbowTermPrefixCode.encode, GorbowFormulaPrefixCode.encode, List.cons_append, List.append_assoc] using StackMeaning.formula (.equal t u) hu
            · simp [step, expand] at hs
              subst next
              cases hm with
              | term t ht => exact StackMeaning.formula (.universalRelation t) ht
            · simp [step, expand] at hs
              subst next
              cases hm with
              | term t ht => exact StackMeaning.formula (.agent t) ht
            · simp [step, expand] at hs
              subst next
              cases hm with
              | term t ht => exact StackMeaning.formula (.knowledgeAll t) ht
            · simp [step, expand] at hs
              subst next
              cases hm with
              | term t ht =>
                  cases ht with
                  | term u hu => simpa only [GorbowTermPrefixCode.encode, GorbowFormulaPrefixCode.encode, List.cons_append, List.append_assoc] using StackMeaning.formula (.knowledge t u) hu
            · simp [step, expand] at hs
              subst next
              cases hm with
              | term t ht => exact StackMeaning.formula (.truth t) ht
            · simp [step, expand] at hs
              subst next
              cases hm with
              | formula φ ht => exact StackMeaning.formula (.neg φ) ht
            · simp [step, expand] at hs
              subst next
              cases hm with
              | formula φ ht =>
                  cases ht with
                  | formula ψ hu => simpa only [GorbowTermPrefixCode.encode, GorbowFormulaPrefixCode.encode, List.cons_append, List.append_assoc] using StackMeaning.formula (.imp φ ψ) hu
            · simp [step, expand] at hs
              subst next
              cases hm with
              | formula φ ht =>
                  cases ht with
                  | formula ψ hu => simpa only [GorbowTermPrefixCode.encode, GorbowFormulaPrefixCode.encode, List.cons_append, List.append_assoc] using StackMeaning.formula (.conj φ ψ) hu
            · simp [step, expand] at hs
              subst next
              cases hm with
              | formula φ ht =>
                  cases ht with
                  | formula ψ hu => simpa only [GorbowTermPrefixCode.encode, GorbowFormulaPrefixCode.encode, List.cons_append, List.append_assoc] using StackMeaning.formula (.disj φ ψ) hu
            · simp [step, expand] at hs
              subst next
              cases hm with
              | formula φ ht => exact StackMeaning.formula (.all φ) ht
            · simp [step, expand] at hs
              subst next
              cases hm with
              | formula φ ht => exact StackMeaning.formula (.ex φ) ht
          · have hx0 : x ≠ 0 := by omega
            have hx1 : x ≠ 1 := by omega
            have hx2 : x ≠ 2 := by omega
            have hx3 : x ≠ 3 := by omega
            have hx4 : x ≠ 4 := by omega
            have hx5 : x ≠ 5 := by omega
            have hx6 : x ≠ 6 := by omega
            have hx7 : x ≠ 7 := by omega
            have hx8 : x ≠ 8 := by omega
            have hx9 : x ≠ 9 := by omega
            have hx10 : x ≠ 10 := by omega
            have hx11 : x ≠ 11 := by omega
            simp [step, expand, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hx9, hx10, hx11] at hs
        · by_cases hx : x < n
          · simp [step, expand, hx] at hs
            subst next
            exact StackMeaning.index x hx hm
          · simp [step, expand, hx] at hs
      · have hk0 : kind ≠ 0 := by omega
        have hk1 : kind ≠ 1 := by omega
        have hk2 : kind ≠ 2 := by omega
        simp [step, expand, hk0, hk1, hk2] at hs

private theorem fold_none (raw : List Nat) : raw.foldl step none = none := by
  induction raw with
  | nil => rfl
  | cons x xs ih => exact ih

private theorem meaning_empty {tasks raw} (h : StackMeaning tasks raw) : raw = [] → tasks = [] := by
  cases h with
  | nil => intro _; rfl
  | index i hi ht => intro he; cases he
  | term t ht => cases t <;> simp [GorbowTermPrefixCode.encode]
  | formula φ ht => cases φ <;> simp [GorbowFormulaPrefixCode.encode]

private theorem empty_meaning (tasks : List Task) : StackMeaning tasks [] ↔ tasks = [] := by
  constructor
  · intro h
    exact meaning_empty h rfl
  · intro h; subst tasks; exact StackMeaning.nil

theorem exactStack : Comparators.GorbowSyntaxValidation.ExactStack := by
  intro tasks raw
  induction raw generalizing tasks with
  | nil => simpa [scan] using (empty_meaning tasks).symm
  | cons x raw ih =>
      constructor
      · intro h
        cases hs : step (some tasks) x with
        | none => simp [scan, List.foldl_cons, hs, fold_none] at h
        | some next =>
            have hn : scan next raw = some [] := by simpa only [scan, List.foldl_cons, hs] using h
            exact retreat tasks x next raw hs ((ih next).mp hn)
      · intro h
        obtain ⟨next, hs, hm⟩ := advance h x raw rfl
        simpa only [scan, List.foldl_cons, hs] using (ih next).mpr hm

theorem exactTypedDomain : Comparators.GorbowSyntaxValidation.ExactTypedDomain := by
  constructor
  · intro n raw
    rw [validTerm, decide_eq_true_eq, exactStack]
    constructor
    · intro h
      cases h with
      | term t ht =>
          cases ht
          exact ⟨t, (GorbowTermPrefixCodeProof.decoderExact n _ t).mpr (List.append_nil _)⟩
    · rintro ⟨t, ht⟩
      have he := (GorbowTermPrefixCodeProof.decoderExact n raw t).mp ht
      subst raw
      simpa only [List.append_nil] using StackMeaning.term t StackMeaning.nil
  · intro n raw
    rw [validFormula, decide_eq_true_eq, exactStack]
    constructor
    · intro h
      cases h with
      | formula φ ht =>
          cases ht
          exact ⟨φ, (GorbowFormulaPrefixCodeProof.decoderExact n _ φ).mpr (List.append_nil _)⟩
    · rintro ⟨φ, ht⟩
      have he := (GorbowFormulaPrefixCodeProof.decoderExact n raw φ).mp ht
      subst raw
      simpa only [List.append_nil] using StackMeaning.formula φ StackMeaning.nil

private theorem pr_expand : Primrec (fun p : Task × Nat => expand p.1 p.2) := by
  have hn : Primrec (fun p : Task × Nat => p.1.2) := Primrec.snd.comp Primrec.fst
  have hk (k : Nat) : PrimrecPred (fun p : Task × Nat => p.1.1 = k) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const k)
  have he (k : Nat) : PrimrecPred (fun p : Task × Nat => p.2 = k) :=
    Primrec.eq.comp Primrec.snd (Primrec.const k)
  have hsingle (k : Nat) : Primrec (fun p : Task × Nat => some [(k,p.1.2)]) :=
    Primrec.option_some.comp (Primrec.list_cons.comp ((Primrec.const k).pair hn) (Primrec.const []))
  have hdouble (k : Nat) : Primrec (fun p : Task × Nat => some [(k,p.1.2),(k,p.1.2)]) :=
    Primrec.option_some.comp (Primrec.list_cons.comp ((Primrec.const k).pair hn)
      (Primrec.list_cons.comp ((Primrec.const k).pair hn) (Primrec.const [])))
  have hlift : Primrec (fun p : Task × Nat => some [(1,p.1.2+1)]) :=
    Primrec.option_some.comp (Primrec.list_cons.comp
      ((Primrec.const 1).pair (Primrec.succ.comp hn)) (Primrec.const []))
  have ht := Primrec.ite (he 0) (hsingle 2)
    (Primrec.ite (he 1) (Primrec.const (some ([] : List Task)))
      (Primrec.ite ((he 2).or (he 5)) (hsingle 0)
        (Primrec.ite ((he 3).or (he 4)) (hdouble 0) (Primrec.const none))))
  have hf := Primrec.ite ((he 0).or (he 4)) (hdouble 0)
    (Primrec.ite ((he 1).or ((he 2).or ((he 3).or (he 5)))) (hsingle 0)
      (Primrec.ite (he 6) (hsingle 1)
        (Primrec.ite ((he 7).or ((he 8).or (he 9))) (hdouble 1)
          (Primrec.ite ((he 10).or (he 11)) hlift (Primrec.const none)))))
  have hi := Primrec.ite (Primrec.nat_lt.comp Primrec.snd hn)
    (Primrec.const (some ([] : List Task))) (Primrec.const none)
  exact Primrec.ite (hk 0) ht (Primrec.ite (hk 1) hf (Primrec.ite (hk 2) hi (Primrec.const none)))

private theorem pr_stepList : Primrec (fun p : List Task × Nat =>
    match p.1 with
    | [] => (none : State)
    | task :: rest => (expand task p.2).map (fun added => added ++ rest)) := by
  have he : Primrec (fun p : (List Task × Nat) × (Task × List Task) => expand p.2.1 p.1.2) :=
    pr_expand.comp ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp Primrec.fst))
  have hm : Primrec (fun p : ((List Task × Nat) × (Task × List Task)) × List Task =>
      p.2 ++ p.1.2.2) :=
    Primrec.list_append.comp Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have h := Primrec.list_casesOn Primrec.fst (Primrec.const none) (Primrec.option_map he hm.to₂).to₂
  apply h.of_eq
  intro p
  cases p.1 <;> rfl

private theorem pr_step : Primrec (fun p : State × Nat => step p.1 p.2) := by
  have h := Primrec.option_bind (Primrec.fst : Primrec (fun p : State × Nat => p.1))
    (pr_stepList.comp (Primrec.snd.pair (Primrec.snd.comp Primrec.fst))).to₂
  apply h.of_eq
  intro p
  rcases p with ⟨state, token⟩
  cases state with
  | none => rfl
  | some tasks =>
      cases tasks with
      | nil => rfl
      | cons task rest => cases he : expand task token <;> simp [step, he]

private theorem pr_scan : Primrec (fun p : List Task × List Nat => scan p.1 p.2) :=
  Primrec.list_foldl Primrec.snd (Primrec.option_some.comp Primrec.fst)
    (pr_step.comp Primrec.snd).to₂

private theorem pr_valid (kind : Nat) : Primrec (fun p : Nat × List Nat =>
    decide (scan [(kind,p.1)] p.2 = some [])) := by
  have hs : Primrec (fun p : Nat × List Nat => scan [(kind,p.1)] p.2) :=
    pr_scan.comp ((Primrec.list_cons.comp ((Primrec.const kind).pair Primrec.fst)
      (Primrec.const [])).pair Primrec.snd)
  exact (Primrec.eq.comp hs (Primrec.const (some ([] : List Task)))).decide

theorem uniformPrograms : Comparators.GorbowSyntaxValidation.UniformPrograms :=
  ⟨pr_expand, pr_step, pr_scan, pr_valid 0, pr_valid 1⟩

theorem gorbowSyntaxValidation : Comparators.GorbowSyntaxValidation.Target :=
  ⟨exactStack, exactTypedDomain, uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowSyntaxValidationProof
