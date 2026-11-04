module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceEnvironmentComputabilityFormulaProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSubstitutionEnvironment
open Source NumberedRewriteSyntax NumberedLeastCodeRepresentative

def variableAt : (Gamma : List Ty) → (i : Fin Gamma.length) → Variable Gamma (Gamma.get i)
  | [], i => Fin.elim0 i
  | tau :: rest, i => Fin.cases .here (fun j => .there (variableAt rest j)) i

def substitutionValues {n : Nat} {arity : Fin n → Nat} (symbols : List (Fin n)) (S : List Ty)
    {Gamma Delta : List Ty} (theta : NumberedRewriteSyntax.Substitution (Fin n) arity Gamma Delta) : Fin Gamma.length → Nat :=
  fun i => representativeCode symbols S ⟨Gamma.get i,theta (variableAt Gamma i)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSubstitutionEnvironment
