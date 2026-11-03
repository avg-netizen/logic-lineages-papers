module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NativeBetaCasesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryTemplateGraftingProof
public import LogicLineages.OrdinalComparison.SourceFreeOccurrencesProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NativeBetaCasesSupportProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourceTypeSupport Source.SourceFreeOccurrences
open RecursiveComparison LiteralContexts NativeBetaCases

private theorem emptyWith {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) (env : MarkedSubstitution Symbol arity Γ Δ) :
    applyOriginalWith q env .nil rfl=some (substituteTerm q env) := by cases q <;> rfl

theorem originalBetaApplication {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {σ τ : Ty}
    (body : Term Symbol arity (σ::Γ) τ) (p : MarkedTerm Symbol arity Γ σ) :
    applyOriginalWith (embed (.lam body)) (fun v => .var v) (.cons p .nil) rfl=
      some (substituteTerm (embed body) (extendEnvironment (fun v => .var v) p)) := by
  exact emptyWith (embed body) (extendEnvironment (fun v => .var v) p)

theorem betaEmbedding {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {σ τ : Ty}
    (body : Term Symbol arity (σ::Γ) τ) (arg : Term Symbol arity Γ σ) :
    substituteTerm (embed body) (extendEnvironment (fun v => .var v) (embed arg))=
      embed (body.substitute (Substitution.single arg)) := by
  rw [Source.SourceMarkedBindingProof.embeddingSubstitution Symbol arity (σ::Γ) Γ τ body (Substitution.single arg)]
  apply congrArg (substituteTerm (embed body))
  funext υ v
  cases v <;> rfl

theorem betaSupport {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {σ τ : Ty}
    (body : Term Symbol arity (σ::Γ) τ) (arg : Term Symbol arity Γ σ) :
    typeSupport (body.substitute (Substitution.single arg)) ⊆ typeSupport (.app (.lam body) arg) := by
  rw [Source.SourceFreeOccurrencesProof.exactTypeSupportSubstitution Symbol arity (σ::Γ) Γ τ body (Substitution.single arg)]
  intro ρ hρ
  rcases Finset.mem_union.mp hρ with hb | hi
  · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _ hb))
  have he := (Source.SourceFreeOccurrencesProof.imageTypeSupportMembership Symbol arity (σ::Γ) Γ
    (Substitution.single arg) (freeOccurrences body) ρ).mp hi
  obtain ⟨⟨υ,v⟩,hv,hsub⟩ := he
  cases v with
  | here => exact Finset.mem_union_right _ (Finset.mem_union_right _ hsub)
  | there v =>
      have ht := Source.SourceFreeOccurrencesProof.occurringVariableTypeSupport Symbol arity (σ::Γ) τ body ⟨υ,.there v⟩ hv
      have hm : ρ ∈ υ.subtypes := by simpa [Substitution.single,typeSupport] using hsub
      have hb := Source.SourceTypeSupportProof.subtypeClosedSupport Symbol arity (σ::Γ) τ body υ ht ρ hm
      exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _ hb))

end LogicLineages.OrdinalComparison.TerminationOrdering.NativeBetaCasesSupportProof
