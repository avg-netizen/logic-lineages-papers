module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSubstitutionEnvironmentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSubstitutionEnvironmentTargets
open Source NumberedRewriteSyntax NumberedLeastCodeRepresentative PositiveArithmeticOperators SourceComputabilityFormula
open SourceEnvironmentComputabilityFormula SourceSubstitutionEnvironment

def ActualVariableAtIndex : Prop := ∀ (Gamma : List Ty) (i : Fin Gamma.length),
  SourceTypedPorts.variableIndex (variableAt Gamma i) = i.val

def ActualVariableAtExhaustive : Prop := ∀ (Gamma : List Ty) (tau : Ty) (v : Variable Gamma tau),
  ∃ i : Fin Gamma.length, (⟨Gamma.get i,variableAt Gamma i⟩ : Sigma (Variable Gamma)) = ⟨tau,v⟩

def ActualSubstitutionEnvironmentFormula : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Delta : List Ty)
    (formulas : Ty → language.Formula (Fin 2)),
  (∀ tau P context value, realize P (formulas tau) ![context,value] ↔ Computable n arity Delta P context tau value) →
  ∀ (symbols : List (Fin n)) (S Gamma : List Ty)
    (theta : NumberedRewriteSyntax.Substitution (Fin n) arity Gamma Delta) (P : Nat → Prop) (context : Nat),
  realize P (environmentFormula formulas Gamma) (Sum.elim (fun _ => context) (substitutionValues symbols S theta)) ↔
    ∀ (tau : Ty) (v : Variable Gamma tau),
      Computable n arity Delta P context tau (representativeCode symbols S ⟨tau,theta v⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSubstitutionEnvironmentTargets
