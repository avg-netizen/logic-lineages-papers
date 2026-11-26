module
public import LogicLineages.OrdinalComparison.GroundSourceEqualityDefinitions
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentDefinitions
public import LogicLineages.OrdinalComparison.WWOriginalDomainDefinitions

@[expose] public section
namespace LogicLineages.StandardControlCurrent.DefaultSourceTargets
open OrdinalComparison Source Source.OriginalDomain

/-- The original domain, not an unrestricted ordinal valuation surrogate. -/
def GroundDomain : Prop :=
  (∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
    ∀ ρ : OrdinalComponent Γ → Nat, (∀ c, 0 < ρ c) →
      ∃ s : AdmissibleSubstitution Γ, ∀ c, valuation s c = (ρ c : Ordinal)) ∧
  (∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
    ∀ s : AdmissibleSubstitution Γ,
      ∃ ρ : OrdinalComponent Γ → Nat, (∀ c, 0 < ρ c) ∧
        ∀ c, valuation s c = (ρ c : Ordinal))

def Assignment : Prop :=
  Primrec (fun x : List Nat × Nat => DefaultSourceAssignment.assignmentCode x.1 x.2) ∧
  (∀ (Γ : List Ty) (τ : Ty) (t : OriginalTerm Γ τ),
    DefaultSourceAssignment.assignmentCode (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm t) =
      (AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t).map OrdinalSyntax.vectorCode) ∧
  (∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
    ∀ (τ : Ty) (t : OriginalTerm Γ τ), ∃ v : OrdinalVector Γ τ.level,
      AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some v)

noncomputable def vectorAt {Γ : List Ty} {n : Nat} (v : OrdinalVector Γ n)
    (s : AdmissibleSubstitution Γ) (j : Nat) : Ordinal :=
  if h : j < n+1 then expressionValue s (v ⟨j,h⟩) else 0

/-- Complete concrete default-policy equality algorithm on the genuine
original admissible substitutions. No source normalization is performed. -/
def Equality : Prop :=
  Computable (fun x : Nat × Nat × Nat => GroundSourceEquality.sourceEqualityCode x.1 x.2.1 x.2.2) ∧
  ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
    ∀ (τ υ : Ty) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ),
      GroundSourceEquality.sourceEqualityCode Γ.length (SyntaxCode.encodeTerm a) (SyntaxCode.encodeTerm b) = true ↔
        ∃ (av : OrdinalVector Γ τ.level) (bv : OrdinalVector Γ υ.level),
          AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy a = some av ∧
          AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy b = some bv ∧
          ∀ (s : AdmissibleSubstitution Γ) (j : Nat), vectorAt av s j = vectorAt bv s j

/-- Supporting fixed-policy instance, not the arbitrary computable-policy theorem. -/
def FullDefaultSource : Prop := GroundDomain ∧ Assignment ∧ Equality
end LogicLineages.StandardControlCurrent.DefaultSourceTargets
