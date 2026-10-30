module

public import LogicLineages.OrdinalComparison.SourceMarkedBindingTargets
public import LogicLineages.OrdinalComparison.SourceMarkedSyntaxProof
public import LogicLineages.OrdinalComparison.SourceStructural

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMarkedBindingProof
open SourceMarkedSyntax SourceMarkedBinding SourceMarkedBindingTargets

theorem markedRenamingIdentity : MarkedRenamingIdentity := by
  constructor
  · intro Symbol arity Γ τ q
    induction q using MarkedTerm.rec
      (motive_2 := fun Γ types a => renameArguments a (fun v => v) = a) <;>
      simp only [renameTerm, renameArguments, Renaming.lift_identity, *]
  · intro Symbol arity Γ types a
    induction a using Arguments.rec
      (motive_1 := fun Γ τ q => renameTerm q (fun v => v) = q) <;>
      simp only [renameTerm, renameArguments, Renaming.lift_identity, *]

private theorem lift_identity {Symbol : Type} (arity : Symbol → Nat) (Γ : List Ty) (τ : Ty) :
    @liftSubstitution Symbol arity Γ Γ τ
      (fun {σ : Ty} (v : Variable Γ σ) => (MarkedTerm.var v : MarkedTerm Symbol arity Γ σ)) =
      fun {σ : Ty} (v : Variable (τ :: Γ) σ) =>
        (MarkedTerm.var v : MarkedTerm Symbol arity (τ :: Γ) σ) := by
  funext σ v
  cases v <;> rfl

theorem markedSubstitutionIdentity : MarkedSubstitutionIdentity := by
  constructor
  · intro Symbol arity Γ τ q
    induction q using MarkedTerm.rec
      (motive_2 := fun Γ types a => substituteArguments a (fun v => .var v) = a) <;>
      simp only [substituteTerm, substituteArguments, lift_identity, *]
  · intro Symbol arity Γ types a
    induction a using Arguments.rec
      (motive_1 := fun Γ τ q => substituteTerm q (fun v => .var v) = q) <;>
      simp only [substituteTerm, substituteArguments, lift_identity, *]

private theorem rename_ground {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty}
    (n : Nat) (f : Fin n → MarkedTerm Symbol arity Γ .ground) (ρ : Renaming Γ Δ) :
    renameArguments (groundArguments n f) ρ = groundArguments n (fun i => renameTerm (f i) ρ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [groundArguments, renameArguments, ih]

theorem embeddingRenaming : EmbeddingRenaming := by
  intro Symbol arity Γ Δ τ t ρ
  induction t generalizing Δ with
  | var v => rfl
  | app f a ihf iha => simp only [Term.rename, embed, renameTerm, renameArguments, ihf Δ ρ, iha Δ ρ]
  | lam body ih => simp only [Term.rename, embed, renameTerm, ih _ ρ.lift]
  | zeroC => rfl
  | succC => rfl
  | caseC τ => rfl
  | recC τ => rfl
  | ranked s args ih =>
    simp only [Term.rename, embed, renameTerm, rename_ground]
    apply congrArg (MarkedTerm.ordinary (.ranked s))
    have hf := congrArg (groundArguments (arity s)) (funext fun i => ih i Δ ρ)
    exact hf.trans (rename_ground (arity s) (fun i => embed (args i)) ρ).symm

private theorem embedded_lift {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty} {τ : Ty}
    (s : Substitution Symbol arity Γ Δ) :
    (fun {σ : Ty} (v : Variable (τ :: Γ) σ) => embed (Substitution.lift s v)) =
      @liftSubstitution Symbol arity Γ Δ τ
        (fun {σ : Ty} (v : Variable Γ σ) => embed (s v)) := by
  funext σ v
  cases v with
  | here => rfl
  | there v => exact embeddingRenaming Symbol arity _ _ _ (s v) _

private theorem substitute_ground {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty}
    (n : Nat) (f : Fin n → MarkedTerm Symbol arity Γ .ground) (s : MarkedSubstitution Symbol arity Γ Δ) :
    substituteArguments (groundArguments n f) s =
      groundArguments n (fun i => substituteTerm (f i) s) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [groundArguments, substituteArguments, ih]

theorem embeddingSubstitution : EmbeddingSubstitution := by
  intro Symbol arity Γ Δ τ t s
  induction t generalizing Δ with
  | var v => rfl
  | app f a ihf iha =>
    simp only [Term.substitute, embed, substituteTerm, substituteArguments, ihf Δ s, iha Δ s]
  | lam body ih =>
    simp only [Term.substitute, embed, substituteTerm]
    rw [← embedded_lift]
    exact congrArg MarkedTerm.lam (ih _ s.lift)
  | zeroC => rfl
  | succC => rfl
  | caseC τ => rfl
  | recC τ => rfl
  | ranked head args ih =>
    simp only [Term.substitute, embed, substituteTerm, substitute_ground]
    apply congrArg (MarkedTerm.ordinary (.ranked head))
    have hf := congrArg (groundArguments (arity head)) (funext fun i => ih i Δ s)
    exact hf.trans (substitute_ground (arity head) (fun i => embed (args i)) (fun v => embed (s v))).symm

end LogicLineages.OrdinalComparison.Source.SourceMarkedBindingProof
