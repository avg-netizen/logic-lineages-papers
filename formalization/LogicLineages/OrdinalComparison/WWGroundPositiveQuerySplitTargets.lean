module
public import LogicLineages.OrdinalComparison.WWGroundPositiveQuerySplitDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundPositiveQuerySplit.Targets
open ForwardTranslation
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def FlagPrimitiveRecursive : Prop := Primrec positiveFlagCode

def ActualScalar : Prop := ∀ (Γ : List Ty) (hΓ : ∀ σ ∈ Γ, σ=Ty.ground)
    (τ : Ty) (t : OriginalTerm Γ τ) (ρ : OrdinalComponent Γ → Nat),
  ∃ v : OrdinalVector Γ τ.level,
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t=some v ∧
    denote (fun c => ((ρ c+1 : Nat) : Ordinal)) (v 0)=(scalarValue ρ t : Ordinal) ∧
    0 < scalarValue ρ t

def PositiveFlagExact : Prop := ∀ (Γ : List Ty) (hΓ : ∀ σ ∈ Γ, σ=Ty.ground)
    (τ υ : Ty) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ) (ρ : OrdinalComponent Γ → Nat),
  ∃ (av : OrdinalVector Γ τ.level) (bv : OrdinalVector Γ υ.level),
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy a=some av ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy b=some bv ∧
    (positiveFlagCode (Γ.length,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)=true ↔
      ∀ j : Nat, sourceVectorAtValue av (fun c => ρ c+1) (j+1) ≤
        sourceVectorAtValue bv (fun c => ρ c+1) (j+1))

/-- Pointwise split on actual typed sources of arbitrary output types. The
positive test is uniform primitive-recursive closed code; the scalar part is
actual full assignment at the SAME original valuation. No effectivity or
whole decision-equivalence theorem is claimed by this supplier. -/
def QuerySplit : Prop := ∀ (Γ : List Ty) (hΓ : ∀ σ ∈ Γ, σ=Ty.ground)
    (τ υ : Ty) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ)
    (ρ : OrdinalComponent Γ → Nat) (strict : Bool),
  QueryAt strict a b ρ ↔
    positiveFlagCode (Γ.length,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)=true ∧
      (if strict then scalarValue ρ a < scalarValue ρ b else scalarValue ρ a ≤ scalarValue ρ b)
end LogicLineages.OrdinalComparison.Source.GroundPositiveQuerySplit.Targets
