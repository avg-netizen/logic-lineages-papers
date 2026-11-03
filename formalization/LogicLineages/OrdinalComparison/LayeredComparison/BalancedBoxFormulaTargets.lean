module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormulaDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormula.Targets
open BalancedSyntax BalancedSmallBox

/-- Exact finite-box truth for ALL raw valuations and typed certificates.
Neither positivity nor genuineness is a premise of the first equivalence:
the positive box at the ORIGINAL L is part of its right-hand side. The
small-branch corollary needs exactly the accepted lower-certificate and
ambient-positivity hypotheses. Outside original support is unrestricted. -/
def ExactFiniteBoxFormula : Prop :=
  (∀ (k : Nat) (Γ : List Nat) (C : Certificate (k :: Γ))
    (E F : Upper k) (desired : Int) (ν : Nat → Nat),
    (sourceFormula k Γ C E F desired).eval ν ↔
      (∀ i ∈ sourceAmbient k Γ C E F, 0 < ν i ∧ ν i < originalThreshold E F) ∧
      Int.sign ((value (k :: Γ) C E ν : Int) - (value (k :: Γ) C F ν : Int)) = desired) ∧
  (∀ (k : Nat) (Γ : List Nat) (C : Certificate (k :: Γ))
    (E F : Upper k) (desired : Int) (ν : Nat → Nat),
    genuineCertificate (k :: Γ) C → positiveOn (sourceAmbient k Γ C E F) ν →
    smallBranch k Γ C E F ν →
    ((sourceFormula k Γ C E F desired).eval ν ↔
      Int.sign ((value (k :: Γ) C E ν : Int) - (value (k :: Γ) C F ν : Int)) = desired))

/-- Literal point encoding and ORIGINAL-support containment, not equality
with the original support after sign filtering. The exact equality here is
only between code variables and the variables of the emitted formula. Raw
numeric outputs also contain no names beyond their original code support. -/
def OriginalSupportAndLiteralCode : Prop :=
  (∀ support word : List Nat, pointCode support word = (pointFormula support word).encode) ∧
  (∀ (k : Nat) (Γ : List Nat) (C : Certificate (k :: Γ))
    (E F : Upper k) (desired : Int),
    BaseFormula.rawVariables (sourceFormula k Γ C E F desired).encode =
      (sourceFormula k Γ C E F desired).variables ∧
    ∀ i ∈ (sourceFormula k Γ C E F desired).variables,
      i ∈ sourceAmbient k Γ C E F) ∧
  (∀ (k : Nat) (Γ : List Nat) (C E F : Nat) (desired : Int),
    ∀ i ∈ BaseFormula.rawVariables (formulaCode k Γ C E F desired),
      i ∈ rawSupport k Γ C E F)

/-- Literal calibration of all raw inputs used by this construction:
deduplicated actual support, ORIGINAL threshold, exact ordered finite words,
and actual signed values at every valid word. The final equality is with the
existing BaseFormula.Formula.encode output, not merely an equivalent code. -/
def ActualSourceCodeCalibration : Prop := ∀ (k : Nat) (Γ : List Nat)
  (C : Certificate (k :: Γ)) (E F : Upper k) (desired : Int),
  let c := BalancedEvaluation.encodeCertificate (k :: Γ) C
  let e := BalancedEvaluation.encodeSyntax (k :: Γ) E
  let f := BalancedEvaluation.encodeSyntax (k :: Γ) F
  rawSupport k Γ c e f = sourceSupport k Γ C E F ∧
  BalancedSourceAdapter.threshold k e f = originalThreshold E F ∧
  rawWords k Γ c e f = boxWords k Γ C E F ∧
  (∀ word ∈ boxWords k Γ C E F,
    codeSign (k :: Γ) c e f (rawSupport k Γ c e f) word =
      Int.sign ((value (k :: Γ) C E (boxValuation k Γ C E F word) : Int) -
        (value (k :: Γ) C F (boxValuation k Γ C E F word) : Int))) ∧
  formulaCode k Γ c e f desired = (sourceFormula k Γ C E F desired).encode

/-- Uniform computability of the actual finite BASE-code constructor on ALL
raw k, shapes, certificate/expression codes and integer desired signs. This
is not conditional on genuine source inputs or another interface theorem.
Malformed codes retain the existing algorithms' defaults. -/
def AllCodeComputation : Prop := Computable (fun p : Input =>
  formulaCode p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormula.Targets
