module

public import LogicLineages.OrdinalComparison.SourceMarkedSyntaxTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMarkedSyntaxProof
open SourceMarkedSyntax SourceMarkedSyntaxTargets

private theorem domain_aux {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) : (markSpine q).isSome = (spineHead q).isSome := by
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) with
  | var v => rfl
  | lam body ih => simpa [markSpine, spineHead] using ih
  | ordinary h args ih => rfl
  | marked h output args types extras ih1 ih2 => rfl
  | nil => trivial
  | cons q rest ih1 ih2 => trivial

theorem markSpineDomain : MarkSpineDomain := fun _ _ _ _ q => domain_aux q

private theorem head_aux {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (q r : MarkedTerm Symbol arity Γ τ) (h : markSpine q = some r) : spineHead r = spineHead q := by
  revert r
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) with
  | var v => intro r h; cases h
  | lam body ih =>
    intro r h
    obtain ⟨body', hb, hr⟩ := Option.map_eq_some_iff.mp h
    subst r
    exact ih body' hb
  | ordinary hd args ih => intro r h; cases h; rfl
  | marked hd output args types extras ih1 ih2 => intro r h; cases h; rfl
  | nil => trivial
  | cons q rest ih1 ih2 => trivial

theorem markSpineHeadPreserved : MarkSpineHeadPreserved := fun _ _ _ _ q r h => head_aux q r h

private theorem idempotent_aux {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) : (markSpine q).bind markSpine = markSpine q := by
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) with
  | var v => rfl
  | lam body ih =>
    cases hb : markSpine body with
    | none => simp [markSpine, hb]
    | some body' =>
      rw [hb] at ih
      simp only [Option.bind_some] at ih
      simp [markSpine, hb, ih]
  | ordinary h args ih => rfl
  | marked h output args types extras ih1 ih2 => rfl
  | nil => trivial
  | cons q rest ih1 ih2 => trivial

theorem markSpineIdempotent : MarkSpineIdempotent := fun _ _ _ _ q => idempotent_aux q

theorem embeddingSpineCalibration : EmbeddingSpineCalibration := by
  intro Symbol arity Γ τ t
  induction t with
  | var v => rfl
  | app f a ihf iha => rfl
  | lam body ih => exact ih
  | zeroC => rfl
  | succC => rfl
  | caseC τ => rfl
  | recC τ => rfl
  | ranked s args ih => rfl

end LogicLineages.OrdinalComparison.Source.SourceMarkedSyntaxProof
