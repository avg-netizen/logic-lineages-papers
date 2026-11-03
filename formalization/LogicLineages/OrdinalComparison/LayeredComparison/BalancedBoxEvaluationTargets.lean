module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluation.Targets
open BalancedSyntax BalancedEvaluation BalancedSmallBox

/-- The EXACT existing joint algorithm is uniformly computable on ALL raw
shape, certificate, expression and finite-table inputs. No validity oracle,
new evaluator, source-only restriction or bounded-code restriction. -/
def AllCodeComputation : Prop := Computable (fun p : Input => joint p)

/-- Literal typed calibration of the existing code functions, at every
finite raw table, including exact ordered support with its repetitions.
There are no genuine-certificate or positivity premises. -/
def ActualSourceCalibration : Prop := ∀ Γ : List Nat, ∀ C : Certificate Γ,
  ∀ E : Syntax Γ, ∀ table : Table,
  codeValue Γ (encodeCertificate Γ C) (encodeSyntax Γ E) table =
    value Γ C E (BaseTermPrograms.valuation table) ∧
  codeVariables Γ (encodeCertificate Γ C) (encodeSyntax Γ E) = rawVariables Γ C E

/-- Concrete table conversion is uniformly computable and pays its exact
lookup equality explicitly. Every accepted finite word evaluates both actual
sources using the existing joint program. An ambient-positive original
small-branch point has its canonical word with the same program results,
ALL original complete inputs and original small-branch truth. -/
def ExactBoxEvaluation : Prop :=
  Computable₂ finiteTable ∧
  (∀ support word : List Nat, word.length = support.length →
    (finiteTable support word).length = tableSize support ∧
    ∀ i : Nat, BaseTermPrograms.valuation (finiteTable support word) i =
      singleCoreBoxLookup support word i) ∧
  (∀ (k : Nat) (Γ : List Nat) (C : Certificate (k :: Γ))
    (E F : Upper k) (word : List Nat), word ∈ boxWords k Γ C E F →
    joint (k :: Γ, encodeCertificate (k :: Γ) C, encodeSyntax (k :: Γ) E,
        boxTable k Γ C E F word) =
      (value (k :: Γ) C E (boxValuation k Γ C E F word), rawVariables (k :: Γ) C E) ∧
    joint (k :: Γ, encodeCertificate (k :: Γ) C, encodeSyntax (k :: Γ) F,
        boxTable k Γ C E F word) =
      (value (k :: Γ) C F (boxValuation k Γ C E F word), rawVariables (k :: Γ) C F) ∧
    completeInputs k Γ C E F (BaseTermPrograms.valuation (boxTable k Γ C E F word)) =
      completeInputs k Γ C E F (boxValuation k Γ C E F word)) ∧
  (∀ (k : Nat) (Γ : List Nat) (C : Certificate (k :: Γ))
    (E F : Upper k) (ν : Nat → Nat), genuineCertificate (k :: Γ) C →
    positiveOn (sourceAmbient k Γ C E F) ν → smallBranch k Γ C E F ν →
    ∃ word : List Nat,
      word = (sourceSupport k Γ C E F).map ν ∧
      word ∈ boxWords k Γ C E F ∧
      (∀ i ∈ sourceAmbient k Γ C E F,
        BaseTermPrograms.valuation (boxTable k Γ C E F word) i = ν i) ∧
      (∀ i, i ∉ sourceAmbient k Γ C E F →
        BaseTermPrograms.valuation (boxTable k Γ C E F word) i = 1) ∧
      joint (k :: Γ, encodeCertificate (k :: Γ) C, encodeSyntax (k :: Γ) E,
          boxTable k Γ C E F word) = (value (k :: Γ) C E ν, rawVariables (k :: Γ) C E) ∧
      joint (k :: Γ, encodeCertificate (k :: Γ) C, encodeSyntax (k :: Γ) F,
          boxTable k Γ C E F word) = (value (k :: Γ) C F ν, rawVariables (k :: Γ) C F) ∧
      completeInputs k Γ C E F (BaseTermPrograms.valuation (boxTable k Γ C E F word)) =
        completeInputs k Γ C E F ν ∧
      smallBranch k Γ C E F (BaseTermPrograms.valuation (boxTable k Γ C E F word)))

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluation.Targets
