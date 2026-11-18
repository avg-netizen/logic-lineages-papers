module
public import LogicLineages.PermittedControl.StandardSourceFactsTargets
public import LogicLineages.OrdinalComparison.ParametricActualCollapseDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.StandardDetectorNumeric
open OrdinalComparison Source Source.AdmissibleSum ParametricActualCollapse

noncomputable def appValue (h : Ordinal) (s q : Nat) : Nat :=
  collapseWith Phi (ordinalNaturalProduct Ordinal.omega0 h + ((s+q : Nat) : Ordinal))

def Calibration : Prop := (∀ a : Ordinal, collapseWith Phi a=actualCollapse a) ∧
  ∀ (h : Ordinal) (s q : Nat), appValue h s q=
    actualCollapse (ordinalNaturalProduct Ordinal.omega0 h + ((s+q : Nat) : Ordinal))

def FiniteTails : Prop :=
  (∀ (a : Ordinal), a<epsilonZero → ∀ s t : Nat, s≤t →
    collapseWith Phi (a+(s : Ordinal))≤collapseWith Phi (a+(t : Ordinal))) ∧
  (∀ (a : Ordinal), a<epsilonZero → Order.IsSuccLimit a → ∀ n : Nat,
    4*collapseWith Phi (a+(n : Ordinal))<collapseWith Phi (a+((n+2 : Nat) : Ordinal))) ∧
  (∀ (a : Ordinal), a<epsilonZero → Order.IsSuccLimit a → ∀ s t q : Nat, s+2≤t →
    4*collapseWith Phi (a+((s+q : Nat) : Ordinal))<
      collapseWith Phi (a+((t+q : Nat) : Ordinal)))

/-- Actual controlled budget is a conclusion, not a caller-supplied oracle. -/
def HeadBudget : Prop := ∀ (a b : Ordinal) (s t q : Nat),
  a<epsilonZero → b<epsilonZero → Order.IsSuccLimit a → Order.IsSuccLimit b → a<b →
  actualOrdinalNorm a≤2*s → s≤q → 5≤q →
  actualOrdinalNorm (a+((s+q+2 : Nat) : Ordinal))≤
    Phi (actualOrdinalNorm (b+((t+q : Nat) : Ordinal))) ∧
  4*collapseWith Phi (a+((s+q : Nat) : Ordinal))<
    collapseWith Phi (b+((t+q : Nat) : Ordinal))

def SourceHeadSeparation : Prop := ∀ (Γ : List Ty) (policy : Policy)
    (ρ : SelectedSourceDomain.AdmissibleSubstitution Phi Γ)
    (a b : OriginalTerm Γ FunctionalDetector.unary) (q : Nat),
  SelectedHardness.value1 Phi policy ρ a<SelectedHardness.value1 Phi policy ρ b →
  SelectedHardness.value0 Phi policy ρ a≤q → 5≤q →
  4*appValue (SelectedHardness.value1 Phi policy ρ a) (SelectedHardness.value0 Phi policy ρ a) q<
    appValue (SelectedHardness.value1 Phi policy ρ b) (SelectedHardness.value0 Phi policy ρ b) q

def SourceScalarSeparation : Prop := ∀ (Γ : List Ty) (policy : Policy)
    (ρ : SelectedSourceDomain.AdmissibleSubstitution Phi Γ)
    (a b : OriginalTerm Γ FunctionalDetector.unary) (q : Nat),
  SelectedHardness.value1 Phi policy ρ a=SelectedHardness.value1 Phi policy ρ b →
  SelectedHardness.value0 Phi policy ρ a+2≤SelectedHardness.value0 Phi policy ρ b →
  4*appValue (SelectedHardness.value1 Phi policy ρ a) (SelectedHardness.value0 Phi policy ρ a) q<
    appValue (SelectedHardness.value1 Phi policy ρ b) (SelectedHardness.value0 Phi policy ρ b) q

def StandardDetectorNumeric : Prop := Calibration ∧ FiniteTails ∧ HeadBudget ∧
  SourceHeadSeparation ∧ SourceScalarSeparation
end LogicLineages.PermittedControl.StandardDetectorNumeric
