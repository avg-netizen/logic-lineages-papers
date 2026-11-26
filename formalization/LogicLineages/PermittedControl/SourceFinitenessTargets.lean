module
public import LogicLineages.PermittedControl.SelectedSourceDomainTargets
public import LogicLineages.PermittedControl.LiteralFinitenessTargets
public import LogicLineages.PermittedControl.LiteralCovarianceTargets
public import LogicLineages.PermittedControl.NakedDeltaProgramTargets
public import LogicLineages.PermittedControl.CountDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.SourceFinitenessTargets
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax SelectedSourceDomain
open StandardControlCurrent

/-- Actual scalar-domain representation, not an assumption of positivity. -/
def ScalarCalibration : Prop :=
  (∀ n : Nat, SelectedSourceDomain.finiteValue (n : Ordinal.{0}) = n ∧
    actualOrdinalNorm (n : Ordinal.{0}) = n) ∧
  (∀ (f : Nat → Nat) (t : ClosedExpression), ClosedGrade f 0 t →
    ∃ n : Nat, closedValue f t = (n : Ordinal.{0}) ∧
      SelectedSourceDomain.finiteValue (closedValue f t) = n ∧ actualOrdinalNorm (closedValue f t) = n) ∧
  (∀ (f : Nat → Nat) (Γ : List Ty) (t : OrdinalExpression Γ), AmbientGrade f Γ 0 t →
    ∀ ρ : SelectedSourceDomain.AdmissibleSubstitution f Γ,
    ∃ n : Nat, expressionValue f ρ t = (n : Ordinal.{0}) ∧
      SelectedSourceDomain.finiteValue (expressionValue f ρ t) = n ∧
      actualOrdinalNorm (expressionValue f ρ t) = n)

def SourcePartial : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (Γ : List Ty) (σ : Ty) (p : Policy), PolicyShape.Effective p →
  ∀ (i : Nat) (t : OrdinalExpression (σ::Γ)), HeadGrade f Γ σ i t →
  ∃! v : OrdinalPartialVector Γ σ,
    AdmissiblePartial.run p i t = some v ∧
    PolicyPartial.run p σ.level i (typedCode t) =
      some (List.ofFn (fun j => typedCode (v j))) ∧
    ∀ j, ordinalLiteralNodes (v j) ≤ 6*3^ordinalLiteralNodes t

def SourceDelta : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (Γ : List Ty) (σ : Ty) (p : Policy), PolicyShape.Effective p →
  ∀ (m : Nat) (h : OrdinalVector (σ::Γ) m), (∀ i, HeadGrade f Γ σ i.val (h i)) →
  ∃! v : OrdinalVector Γ (max (σ.level+1) m),
    LiteralCovariance.delta p h = some v ∧
    NakedDeltaProgram.deltaCode p σ.level m (vectorCode h) = some (vectorCode v)

def SourceAbstraction : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (Γ : List Ty) (σ : Ty) (p : Policy), PolicyShape.Effective p →
  ∀ (m : Nat) (h : OrdinalVector (σ::Γ) m), (∀ i, HeadGrade f Γ σ i.val (h i)) →
  ∃! v : OrdinalVector Γ (max (σ.level+1) m),
    AdmissibleAssignment.abstraction p h = some v ∧
    PolicyAbstraction.abstractionCode p σ.level m (vectorCode h) = some (vectorCode v)

/-- Full Paper17 lem:source-finiteness with literal naked delta, actual graded
success, unique trees, effective programs, and general x-free covariance. -/
def FullSourceFiniteness : Prop :=
  ScalarCalibration ∧ SourcePartial ∧ SourceDelta ∧ SourceAbstraction ∧
  LiteralFinitenessTargets.PartialPrograms ∧ NakedDeltaProgramTargets.Programs ∧
  LiteralFinitenessTargets.DeltaPrograms ∧
  LiteralCovarianceTargets.FullLiteralCovariance ∧ SelectedSourceDomainTargets.DeltaHighRetention

end LogicLineages.PermittedControl.SourceFinitenessTargets
