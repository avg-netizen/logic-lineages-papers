module
public import LogicLineages.OrdinalComparison.GroundSourceEqualityDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.GroundSourceEquality.Targets
open Source Source.ForwardTranslation

def GroundCompiledEquality : Prop :=
  Computable queryEqualityFlag ∧
  ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ=Ty.ground) →
    ∀ (n m : Nat) (a : OrdinalVector Γ n) (b : OrdinalVector Γ m)
      (ac : CompiledVector (OrdinalComponent Γ) n) (bc : CompiledVector (OrdinalComponent Γ) m),
      compileVector a=some ac → compileVector b=some bc →
      (queryEqualityFlag (compiledQueryCode
        (fun c => SourceTypedPorts.variableIndex c.2.1) false ac bc)=true ↔
        ∀ ρ : OrdinalComponent Γ → Nat, (∀ c, 0<ρ c) → SourceEqualityAt a b ρ)

/-- ENTIRE original paper07 cor:sourceeq. The source assignment, scalar
translation, fixed-limit domains, closed positive guards, original numeric
typechecking/compilation and shared-valuation completeness are all owed.
No compiler-success, bound on output/internal types, normal-form or supplied
source-construction certificate is an extra premise. -/
def FullOriginalGroundEquality : Prop :=
  Computable (fun p : Nat × Nat × Nat => sourceEqualityCode p.1 p.2.1 p.2.2) ∧
  ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ=Ty.ground) →
    ∀ (τ υ : Ty) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ),
      sourceEqualityCode Γ.length (SyntaxCode.encodeTerm a) (SyntaxCode.encodeTerm b)=true ↔
        ∃ (av : OrdinalVector Γ τ.level) (bv : OrdinalVector Γ υ.level),
          AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy a=some av ∧
          AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy b=some bv ∧
          ∀ ρ : OrdinalComponent Γ → Nat, (∀ c, 0<ρ c) → SourceEqualityAt av bv ρ

end LogicLineages.OrdinalComparison.GroundSourceEquality.Targets
