module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaComputabilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaComputabilityTargets
open Source PositiveArithmeticOperators PositiveArithmeticTransforms NumberedLeastCodeRepresentative
open JointGammaComputability

def ActualOriginalComputabilityFibers : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (P : Nat → Prop)
    (context : Nat) (tau : Ty) (x : Nat),
  (Computable n arity P context tau (ContextUniform.objectCode Gamma x) ↔
    SourceComputabilityFormula.Computable n arity Gamma
      (fun a => P (tagNumber false (ContextUniform.objectCode Gamma a))) context tau x)

def ActualComputabilityTypedness : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (P : Nat → Prop) (context : Nat) (tau : Ty) (x : Nat),
  Computable n arity P context tau x → JointGammaTyped.encodedTyped n arity context (typeNumber tau) x

def ActualFormulaCalibration : Prop :=
  ∀ (data : Data) (n : Nat) (arity : Fin n → Nat), Calibrated data n arity →
  ∀ (tau : Ty) (P : Nat → Prop) (context x : Nat),
  realize P (formula data tau) ![context,x] ↔ Computable n arity P context tau x

def ActualFiniteWindowCalibration : Prop :=
  ∀ (data : Data) (n : Nat) (arity : Fin n → Nat), Calibrated data n arity →
  ∀ (S : List Ty) (P : Nat → Prop) (context typ x : Nat),
  realize P (SourceFiniteComputabilityFormula.windowFormula (formula data) S) ![context,typ,x] ↔
    ∃ tau ∈ S, typ = typeNumber tau ∧ Computable n arity P context tau x

/-- Actual Programs and literal formulas, calibrated directly against the
EXISTING source computability predicate for every Gamma. This asserts no
closure theorem and does not say that any particular source is computable. -/
def ActualUniformFormulasExist : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), ∃ data : Data, Calibrated data n arity ∧
  (∀ (tau : Ty) (P : Nat → Prop) (context : Nat) (Gamma : List Ty) (x : Nat),
    realize P (formula data tau) ![context,ContextUniform.objectCode Gamma x] ↔
      SourceComputabilityFormula.Computable n arity Gamma
        (fun a => P (tagNumber false (ContextUniform.objectCode Gamma a))) context tau x) ∧
  (∀ (S : List Ty) (P : Nat → Prop) (context typ : Nat) (Gamma : List Ty) (x : Nat),
    realize P (SourceFiniteComputabilityFormula.windowFormula (formula data) S)
      ![context,typ,ContextUniform.objectCode Gamma x] ↔
    ∃ tau ∈ S, typ = typeNumber tau ∧ SourceComputabilityFormula.Computable n arity Gamma
      (fun a => P (tagNumber false (ContextUniform.objectCode Gamma a))) context tau x)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaComputabilityTargets
