module

public import LogicLineages.OrdinalComparison.SourceSpecialApplicationTargets
public import LogicLineages.OrdinalComparison.SourceMarkedBindingProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceSpecialApplicationProof
open SourceMarkedSyntax SourceMarkedBinding SourceSpecialApplication SourceSpecialApplicationTargets

private theorem empty_with {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) (env : MarkedSubstitution Symbol arity Γ Δ) :
    applyOriginalWith q env (Arguments.nil : Arguments Symbol arity Δ []) rfl =
      some (substituteTerm q env) := by
  cases q <;> rfl

theorem emptySpecialApplication : EmptySpecialApplication := by
  intro Symbol arity Γ τ q
  exact (empty_with q (fun v => .var v)).trans
    (congrArg some (SourceMarkedBindingProof.markedSubstitutionIdentity.1 Symbol arity Γ τ q))

theorem originalVariableBlocked : OriginalVariableBlocked := by
  intro Symbol arity Γ Δ ρ τ types v env a rest
  rfl

theorem originalLambdaConsumption : OriginalLambdaConsumption := by
  intro Symbol arity Γ Δ ρ τ types body env a rest
  rfl

theorem functionalOneShotAppend : FunctionalOneShotAppend := by
  constructor
  · intro Symbol arity Γ Δ ρ τ types hd base env a rest h
    rfl
  · intro Symbol arity Γ Δ ρ τ output types extraTypes hd base extras env a rest h
    rfl

theorem originalSpineCounterexample : OriginalSpineCounterexample := by
  exact ⟨rfl, rfl⟩

end LogicLineages.OrdinalComparison.Source.SourceSpecialApplicationProof
