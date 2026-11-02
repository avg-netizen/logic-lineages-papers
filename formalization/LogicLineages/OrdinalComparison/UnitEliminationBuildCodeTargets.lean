module
public import LogicLineages.OrdinalComparison.UnitEliminationBuildCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitEliminationBuildCode.Targets
open OriginalDomain

def ExactFuelBuild : Prop := ∀ (fuel : Nat) (Γ : List Ty) (τ : Ty) (t : OriginalTerm Γ τ),
  buildCode fuel (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm t) =
    (UnitElimination.build fuel t).map UnitEliminationTreeCode.code

def PrimitiveRecursiveSymbolicCompiler : Prop :=
  Primrec (fun p : Nat×List Nat×Nat => buildCode p.1 p.2.1 p.2.2) ∧ Primrec₂ compileCode

/-- Uniform actual-source compilation and actual scalar semantics, with no
success certificate, functional-only output, or source-grammar restriction. -/
def ActualUniformSourceCompiler : Prop := Computable₂ realizedCompileCode ∧
  ∀ (Γ : List Ty) (τ : Ty) (t : OriginalTerm Γ τ),
    ∃ q : UnitElimination.Tree (Nat×Nat) Γ,
      UnitElimination.build (Γ.length+1) t = some q ∧
      compileCode (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm t) = some (UnitEliminationTreeCode.code q) ∧
      realizedCompileCode (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm t) =
        some (UnitEliminationTreeCode.code (UnitElimination.realize q)) ∧
      (∀ s ∈ UnitElimination.sources (UnitElimination.realize q), ∀ σ ∈ s.1, σ=Ty.ground) ∧
      ∀ (ρ : Variable Γ .ground → Nat) (r : Nat),
        UnitElimination.Eval (UnitElimination.realize q) ρ r ↔
          ∃ v : OrdinalVector Γ τ.level,
            AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some v ∧
            expressionValue (UnitObservation.substitution ρ) (v 0) = (r : Ordinal)
end LogicLineages.OrdinalComparison.Source.UnitEliminationBuildCode.Targets
