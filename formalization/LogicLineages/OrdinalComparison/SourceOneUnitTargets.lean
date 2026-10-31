module
public import LogicLineages.OrdinalComparison.SourceOneUnitDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OneUnit.Targets
open AdmissibleAssignment OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- All source-level suppliers used in the printed elimination, proved for
actual assignments rather than assumed as certificates. Literal copy syntax
precedes partial/size analysis; no collected expression replaces that tree. -/
def ActualHeadConstruction : Prop :=
  ∀ (Γ : List Ty) (σ τ : Ty) (a : OriginalTerm (σ :: Γ) τ),
    ∃ h : OrdinalVector (σ :: Γ) τ.level,
    ∃ h' : OrdinalVector (σ :: Γ) (Ty.arrow .ground τ).level,
    ∃ ps ps' : OrdinalPartialVector Γ σ,
    ∃ l : OrdinalVector Γ (Ty.arrow σ τ).level,
    ∃ l' : OrdinalVector Γ (Ty.arrow σ (.arrow .ground τ)).level,
    ∃ d : Data,
      assignment OrdinalSyntax.defaultPolicy a = some h ∧
      assignment OrdinalSyntax.defaultPolicy (unused a) = some h' ∧
      assignment OrdinalSyntax.defaultPolicy (first a) = some l ∧
      assignment OrdinalSyntax.defaultPolicy (second a) = some l' ∧
      AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (h 0) = some ps ∧
      AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (h' 0) = some ps' ∧
      compile a = some d ∧ d.d=multiplier h ∧ d.d'=multiplier h' ∧ d.free=ordinalHeadFree (h 0) ∧
      0 < d.d ∧ h' 0=inflated τ (h 0) ∧
      (d.free=false →
        ordinalPartialSize (h' 0)=coefficient τ*ordinalPartialSize (h 0)+3*copies τ ∧
        (∀ j : Fin (τ.level+1), 0 < j.val →
          ordinalPartialSize (h j) ≤ ordinalPartialSize (h' ⟨j.val, by have := j.isLt; simp only [Ty.level]; omega⟩)) ∧
        d.d < d.d') ∧
      ∀ ρ : AdmissibleSubstitution Γ,
        ∃ P R P' R' L L' : Nat,
          0<P ∧ 0<R ∧ 0<L ∧ 0<L' ∧
          expressionValue ρ (ps 0)=(P : Ordinal) ∧
          expressionValue (unitExtension (σ := σ) ρ) (h 0)=(R : Ordinal) ∧
          expressionValue ρ (ps' 0)=(P' : Ordinal) ∧
          expressionValue (unitExtension (σ := σ) ρ) (h' 0)=(R' : Ordinal) ∧
          expressionValue ρ (l 0)=(L : Ordinal) ∧ expressionValue ρ (l' 0)=(L' : Ordinal) ∧
          L=d.d*P+R ∧
          (d.free=true → P=R+1 ∧ L=(d.d+1)*R+d.d) ∧
          (d.free=false → P'=coefficient τ*P+4*copies τ ∧
            R'=coefficient τ*R+copies τ ∧
            L'=coefficient τ*d.d'*P+coefficient τ*R+constant τ d) ∧
          ∀ r : Nat, Formula ρ a d r ↔ r=R

/-- Whole one-name elimination at any selected free functional name. The two
observed sources have that name actually bound; remaining admissible vectors
(and thus common functional unit observations) are shared. Only scalars are
claimed finite. The original unpermuted source assignment is retained. -/
def FullSourceOneUnit : Prop := ActualHeadConstruction ∧
  ∀ (left right : List Ty) (σ τ : Ty), 0 < σ.level →
    ∀ a : OriginalTerm (left ++ σ :: right) τ,
      ∃ d : Data, compile (a.rename (SelectedBinder.moveToHead left right σ)) = some d ∧
      ∃ h : OrdinalVector (left ++ σ :: right) τ.level,
        assignment OrdinalSyntax.defaultPolicy a = some h ∧
        ∀ ρ : AdmissibleSubstitution (left ++ right), ∃ R : Nat, 0<R ∧
          denote (selectedValuation ρ) (h 0)=(R : Ordinal) ∧
          ∀ r : Nat,
            Formula ρ (a.rename (SelectedBinder.moveToHead left right σ)) d r ↔ r=R
end LogicLineages.OrdinalComparison.Source.OneUnit.Targets
