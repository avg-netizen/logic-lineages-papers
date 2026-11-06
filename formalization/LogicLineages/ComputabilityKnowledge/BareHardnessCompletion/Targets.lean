module
public import LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.Targets
open PositiveExpression WWOrdinalTermSemantics WWGroundAdmissibility WWGroundClasses

def FramingProgram : Prop := Computable framed
def ScalarValidation : Prop :=
  Computable validScalar ∧ ∀ raw, validScalar raw = true ↔ ScalarDomain raw
def ScalarPrograms : Prop := ∀ weak, Computable (scalarProgram weak)
def ScalarCalibration : Prop := ∀ weak p,
  scalarProgram weak (Encodable.encode (PolynomialCircuit.encode p)) = polynomialRaw weak p
def VectorPrograms : Prop := ∀ weak, Computable (vectorProgram weak)
def VectorCalibration : Prop :=
  ∀ (weak : Bool) (e d : Nat) (u v : Expr (Fin d)), u.depth ≤ 2 → v.depth ≤ 2 →
    scalarProgram false e = expressionCode v u → vectorProgram weak e = paddedRaw weak u v

def ScalarUpperBound : Prop :=
  ∀ norm weak, REPred (fun raw => ¬ ScalarComparison norm weak raw)

def PolynomialSourceBridge : Prop :=
  ∀ p : PolynomialCircuit.Code, p.WellFormed → ∀ weak,
    ScalarDomain (polynomialRaw weak p) ∧
    ∀ norm, ¬ PolynomialDomainShift.HasNonnegativeRoot p ↔
      ScalarComparison norm weak (polynomialRaw weak p)

/-- Positivity, finiteness and the original norm are certified over precisely
the occurring-name admissibility domain. Class membership retains every i >= 1. -/
def PositiveSourceFacts : Prop :=
  ∀ (d : Nat) (a : Expr (Fin d)),
    (∀ i : Nat, 1 ≤ i → C d i (embed a)) ∧
    ∀ χ : Fin d → Term Empty, Admissible (support (embed a)) χ →
      ∃ n : Nat, 0 < n ∧ WWClosedAssignment.closedValue (substitute χ (embed a)) =
        (n : Ordinal.{0}) ∧
        LogicLineages.OrdinalComparison.actualOrdinalNorm
          (WWClosedAssignment.closedValue (substitute χ (embed a))) = n

def ScalarHardness : Prop :=
  ∀ weak (P : Nat → Prop), REPred P →
    ∃ f : Nat → ScalarCode, Computable f ∧ ∀ x,
      ScalarDomain (f x) ∧
      (¬ P x ↔ ScalarComparison false weak (f x)) ∧
      (¬ P x ↔ ScalarComparison true weak (f x))

def ScalarCompleteness : Prop :=
  ∀ norm weak, Pi01Complete (ScalarComparison norm weak)

/-- Both value and norm comparison, both order symbols, all original ground
contexts, and uniformly genuine depth-two reduction outputs. -/
def FullFiniteBareHardness : Prop :=
  ScalarHardness ∧ ScalarCompleteness ∧ PositiveSourceFacts

def VectorHardness : Prop :=
  ∀ weak (P : Nat → Prop), REPred P →
    ∃ f : Nat → VectorCode, Computable f ∧ ∀ x,
      VectorDomain (f x) ∧ (¬ P x ↔ VectorComparison weak (f x))

/-- Even a total Boolean procedure required to be correct only on the
genuine bounded two-component inputs cannot decide the original comparison. -/
def VectorUndecidable : Prop := ∀ weak,
  ¬ ∃ decideSource : VectorCode → Bool, Computable decideSource ∧
    ∀ raw, VectorDomain raw → (decideSource raw = true ↔ VectorComparison weak raw)

def FullBoundedBareVectors : Prop := VectorHardness ∧ VectorUndecidable

end LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.Targets
