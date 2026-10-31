module
public import LogicLineages.OrdinalComparison.WWSourceComparisonDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open ForwardTranslation AdmissibleSum AdmissibleAssignment

def CompiledQueryPointCorrect : Prop :=
  ∀ (Γ : List Ty) (n m : Nat) (a : OrdinalVector Γ n) (b : OrdinalVector Γ m)
    (ac : CompiledVector (OrdinalComponent Γ) n) (bc : CompiledVector (OrdinalComponent Γ) m),
    compileVector a = some ac → compileVector b = some bc →
      ∀ (index : OrdinalComponent Γ → Nat) (strict : Bool) (xs : List Nat),
        encodedQueryAt (compiledQueryCode index strict ac bc) xs = true ↔
          SourceComparisonAt strict a b (fun i => xs.getD (index i) 0 + 1)

def ActualSourceQueryCompilation : Prop :=
  ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
    ∀ (τ υ : Ty) (p : Policy) (strict : Bool) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ),
      ∃ av : OrdinalVector Γ τ.level, ∃ bv : OrdinalVector Γ υ.level, ∃ q : EncodedQuery,
        assignment p a = some av ∧ assignment p b = some bv ∧
        compileSourceQuery p strict a b = some q ∧
        (∀ xs : List Nat, encodedQueryAt q xs = true ↔
          SourceComparisonAt strict av bv (fun c => xs.getD (SourceTypedPorts.variableIndex c.2.1) 0 + 1)) ∧
        ((∀ xs : List Nat, xs.length = Γ.length → encodedQueryAt q xs = true) ↔
          ∀ ρ : OrdinalComponent Γ → Nat, (∀ c, 0 < ρ c) → SourceComparisonAt strict av bv ρ)
end LogicLineages.OrdinalComparison.Source.Targets
