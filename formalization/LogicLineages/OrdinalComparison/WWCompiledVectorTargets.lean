module
public import LogicLineages.OrdinalComparison.WWCompiledVectorDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open ForwardTranslation AdmissibleSum AdmissibleAssignment
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def CompiledVectorSound : Prop :=
  ∀ (Γ : List Ty) (n : Nat) (v : OrdinalVector Γ n) (c : CompiledVector (OrdinalComponent Γ) n),
    compileVector v = some c → ∀ ρ : OrdinalComponent Γ → Nat,
      ∀ j, c.value ρ j = denote (fun x => (ρ x : Ordinal)) (v j)

def GeneratedGroundVectorCompilationTotal : Prop :=
  ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
    ∀ (n : Nat) (v : OrdinalVector Γ n), (∀ j, GeneratedOrdinalGrade Γ j.val (v j)) →
      ∃ c, compileVector v = some c

def ActualSourceVectorCompilation : Prop :=
  ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
    ∀ (τ : Ty) (p : Policy) (t : OriginalTerm Γ τ),
      ∃ v : OrdinalVector Γ τ.level, assignment p t = some v ∧
        ∃ c : CompiledVector (OrdinalComponent Γ) τ.level, compileVector v = some c ∧
          ∀ ρ : OrdinalComponent Γ → Nat, ∀ j,
            c.value ρ j = denote (fun x => (ρ x : Ordinal)) (v j)
end LogicLineages.OrdinalComparison.Source.Targets
