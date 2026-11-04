module
public import LogicLineages.OrdinalComparison.SourceTypedCodeAdequacyDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceTypedCodeAdequacy.Targets

def FixedContextTypeUniqueness : Prop := ∀ (Γ : List Ty) (τ υ : Ty)
  (t : OriginalTerm Γ τ) (u : OriginalTerm Γ υ),SyntaxCode.erase t=SyntaxCode.erase u → τ=υ

def TypedCodeInjective : Prop := ∀ (Γ : List Ty) (τ : Ty),
  Function.Injective (SyntaxCode.encodeTerm (Γ:=Γ) (τ:=τ))

def GenericControlTransport : Prop :=
  (∀ (Γ : List Ty) (τ : Ty) (t u : OriginalTerm Γ τ),SameCode t u →
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t=
      AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy u) ∧
  (∀ (G : Nat → Nat) (Γ : List Ty) (t u : OriginalTerm Γ .ground),SameCode t u →
    (∀ (ν : OrdinalComponent Γ → Ordinal) (n : Nat),
      ParametricSourceEraser.Scalar G ν t n ↔ ParametricSourceEraser.Scalar G ν u n) ∧
    (∀ (ρ : OrdinalComponent Γ → Nat) (y : Nat),
      ParametricSourceSuccessor.Observation G ρ t y ↔ ParametricSourceSuccessor.Observation G ρ u y))
end LogicLineages.OrdinalComparison.Source.SourceTypedCodeAdequacy.Targets
