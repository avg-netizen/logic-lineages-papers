module
public import LogicLineages.OrdinalComparison.TerminationOrdering.HeadClosureTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.Proof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding

theorem renameAllowed {Symbol : Type} {arity : Symbol → Nat}
    (P : Head Symbol → Prop) {Γ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) :
    ∀ {Δ : List Ty} (ρ : Renaming Γ Δ),
      headsAllowed P q → headsAllowed P (renameTerm q ρ) := by
  induction q using MarkedTerm.rec
    (motive_2 := fun Γ types args => ∀ {Δ : List Ty} (ρ : Renaming Γ Δ),
      argumentsAllowed P args → argumentsAllowed P (renameArguments args ρ)) with
  | var v => intro Δ ρ h; trivial
  | lam body ih => intro Δ ρ h; exact ih ρ.lift h
  | ordinary hd base ih => intro Δ ρ h; exact ⟨h.1, ih ρ h.2⟩
  | marked hd output base extraTypes extras ihb ihe =>
      intro Δ ρ h
      exact ⟨h.1, ihb ρ h.2.1, ihe ρ h.2.2⟩
  | nil => trivial
  | cons q rest ihq ihr =>
      rename_i Δ ρ h
      exact ⟨ihq ρ h.1, ihr ρ h.2⟩

theorem renamingHeadClosure : Targets.RenamingHeadClosure := by
  intro Symbol arity P Γ Δ τ q ρ h
  exact renameAllowed P q ρ h

theorem markingHeadClosure : Targets.MarkingHeadClosure := by
  intro Symbol arity P Γ τ q
  induction q using MarkedTerm.rec
    (motive_2 := fun _ _ _ => True) with
  | var v => intro r h he; cases he
  | lam body ih =>
      intro r h he
      simp only [markSpine] at he
      cases hm : markSpine body with
      | none => simp [hm] at he
      | some out =>
          simp only [hm, Option.map_some, Option.some.injEq] at he
          subst r
          exact ih out h hm
  | ordinary hd base ih =>
      intro r h he
      cases he
      exact ⟨h.1, h.2, True.intro⟩
  | marked hd output base extraTypes extras ihb ihe =>
      intro r h he
      cases he
      exact h
  | nil => trivial
  | cons q rest ihq ihr => trivial

private theorem liftAllowed {Symbol : Type} {arity : Symbol → Nat}
    (P : Head Symbol → Prop) {Γ Δ : List Ty} {τ : Ty}
    (env : MarkedSubstitution Symbol arity Γ Δ) (h : substitutionAllowed P env) :
    substitutionAllowed P (@liftSubstitution Symbol arity Γ Δ τ env) := by
  intro σ v
  cases v with
  | here => trivial
  | there v => exact renameAllowed P (env v) (Renaming.weaken Δ τ) (h v)

theorem substituteAllowed {Symbol : Type} {arity : Symbol → Nat}
    (P : Head Symbol → Prop) {Γ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) :
    ∀ {Δ : List Ty} (env : MarkedSubstitution Symbol arity Γ Δ),
      headsAllowed P q → substitutionAllowed P env →
      headsAllowed P (substituteTerm q env) := by
  induction q using MarkedTerm.rec
    (motive_2 := fun Γ types args => ∀ {Δ : List Ty}
      (env : MarkedSubstitution Symbol arity Γ Δ),
      argumentsAllowed P args → substitutionAllowed P env →
      argumentsAllowed P (substituteArguments args env)) with
  | var v => intro Δ env h he; exact he v
  | lam body ih => intro Δ env h he; exact ih (liftSubstitution env) h (liftAllowed P env he)
  | ordinary hd base ih => intro Δ env h he; exact ⟨h.1, ih env h.2 he⟩
  | marked hd output base extraTypes extras ihb ihe =>
      intro Δ env h he
      exact ⟨h.1, ihb env h.2.1 he, ihe env h.2.2 he⟩
  | nil => trivial
  | cons q rest ihq ihr =>
      rename_i Δ env h he
      exact ⟨ihq env h.1 he, ihr env h.2 he⟩

theorem substitutionHeadClosure : Targets.SubstitutionHeadClosure := by
  intro Symbol arity P Γ Δ τ q env h he
  exact substituteAllowed P q env h he

private theorem transportAllowed {Symbol : Type} {arity : Symbol → Nat}
    (P : Head Symbol → Prop) {Γ : List Ty} {σ τ : Ty} (h : σ = τ)
    (q : MarkedTerm Symbol arity Γ σ) (hq : headsAllowed P q) :
    headsAllowed P (Source.SourceSpecialApplication.transportTerm h q) := by
  cases h
  exact hq

open Source.SourceSpecialApplication

private theorem appendAllowed {Symbol : Type} {arity : Symbol → Nat}
    (P : Head Symbol → Prop) {Γ xs : List Ty} (a : Arguments Symbol arity Γ xs) :
    ∀ {ys : List Ty} (b : Arguments Symbol arity Γ ys),
      argumentsAllowed P a → argumentsAllowed P b → argumentsAllowed P (appendArguments a b) := by
  induction a using Arguments.rec (motive_1 := fun _ _ _ => True) with
  | var v => trivial
  | lam body ih => trivial
  | ordinary hd base ih => trivial
  | marked hd output base extraTypes extras ihb ihe => trivial
  | nil => intro ys b ha hb; exact hb
  | cons q rest ihq ihr => intro ys b ha hb; exact ⟨ha.1, ihr b ha.2 hb⟩

private theorem emptyAllowed {Symbol : Type} {arity : Symbol → Nat}
    (P : Head Symbol → Prop) {Γ Δ : List Ty} {σ τ : Ty}
    (q : MarkedTerm Symbol arity Γ σ) (env : MarkedSubstitution Symbol arity Γ Δ)
    (h : σ = τ) (r : MarkedTerm Symbol arity Δ τ)
    (hq : headsAllowed P q) (he : substitutionAllowed P env)
    (hr : applyOriginalWith q env (.nil : Arguments Symbol arity Δ []) h = some r) :
    headsAllowed P r := by
  have hn : applyOriginalWith q env (.nil : Arguments Symbol arity Δ []) h =
      some (transportTerm h (substituteTerm q env)) := by
    cases q <;> rfl
  rw [hn] at hr
  have hh := Option.some.inj hr
  rw [← hh]
  exact transportAllowed P h _ (substituteAllowed P q env hq he)

theorem applicationAllowed {Symbol : Type} {arity : Symbol → Nat}
    (P : Head Symbol → Prop) {Γ : List Ty} {σ : Ty} (q : MarkedTerm Symbol arity Γ σ) :
    ∀ {Δ types : List Ty} {τ : Ty} (env : MarkedSubstitution Symbol arity Γ Δ)
      (args : Arguments Symbol arity Δ types) (h : σ = arrows types τ)
      (r : MarkedTerm Symbol arity Δ τ),
      headsAllowed P q → substitutionAllowed P env → argumentsAllowed P args →
      applyOriginalWith q env args h = some r → headsAllowed P r := by
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) with
  | var v =>
      intro Δ types τ env args h r hq he ha hr
      cases args with
      | nil => exact emptyAllowed P (.var v) env h r hq he hr
      | cons a rest => simp [applyOriginalWith] at hr
  | lam body ih =>
      intro Δ types τ env args h r hq he ha hr
      cases args with
      | nil => exact emptyAllowed P (.lam body) env h r hq he hr
      | cons a rest =>
          have hc := Ty.arrow.inj h
          have ha' := transportAllowed P hc.1.symm a ha.1
          have hh : substitutionAllowed P (extendEnvironment env (transportTerm hc.1.symm a)) := by
            intro υ v
            cases v with
            | here => exact ha'
            | there v => exact he v
          exact ih (extendEnvironment env (transportTerm hc.1.symm a)) rest hc.2 r hq hh ha.2 hr
  | ordinary hd base ih =>
      intro Δ types τ env args h r hq he ha hr
      cases args with
      | nil => exact emptyAllowed P (.ordinary hd base) env h r hq he hr
      | cons a rest =>
          have hs := substituteAllowed P (.ordinary hd base) env hq he
          simp only [applyOriginalWith] at hr
          have hh := Option.some.inj hr
          rw [← hh]
          exact ⟨hs.1, hs.2, ha⟩
  | marked hd output base extraTypes extras ihb ihe =>
      intro Δ types τ env args h r hq he ha hr
      cases args with
      | nil => exact emptyAllowed P (.marked hd output base extraTypes extras) env h r hq he hr
      | cons a rest =>
          have hs := substituteAllowed P (.marked hd output base extraTypes extras) env hq he
          simp only [applyOriginalWith] at hr
          have hh := Option.some.inj hr
          rw [← hh]
          exact ⟨hs.1, hs.2.1, appendAllowed P _ _ hs.2.2 ha⟩
  | nil => trivial
  | cons q rest ihq ihr => trivial

theorem simultaneousApplicationHeadClosure : Targets.SimultaneousApplicationHeadClosure := by
  intro Symbol arity P Γ Δ σ τ types q env args h r hq he ha hr
  exact applicationAllowed P q env args h r hq he ha hr

end LogicLineages.OrdinalComparison.TerminationOrdering.Proof
