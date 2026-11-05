module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadFirstOrderDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadFirstOrderTargets
open CommonHeadFirstOrder

/-- Arbitrary Boolean structure and quantifier alternation, preserving every atom's
own actual source certificate and the current environment at each binder. -/
def ActualSourceTranslation : Prop := ∀ p : Formula, p.certified → ∀ ν,
  (translate p).eval ν ↔ p.eval ν

/-- Exact free-variable SET, including under shadowing and positive-domain guards.
No validity premise is required by this literal syntax property. -/
def ExactFreeVariables : Prop := ∀ (p : Formula) i,
  i ∈ (translate p).variables ↔ i ∈ p.variables

/-- Actual output natural code of the existing SourceFormula grammar. -/
def LiteralCodeCalibration : Prop := ∀ p : Formula,
  Code.translate p.encode = (translate p).encode

/-- Decoding and interpreting the actual emitted code gives the actual source
truth. This is a translation, NOT a decision algorithm for that truth. -/
def ActualSourceCode : Prop := ∀ p : Formula, p.certified → ∀ ν,
  (SourceFormulaCodec.decode (Code.translate p.encode)).eval ν ↔ p.eval ν

/-- Total raw-code computation, including explicit malformed atomic defaults. -/
def ActualNumericProgram : Prop := Computable Code.translate

/-- Both universal domains are retained exactly via ordinary negation/existential
syntax; positive quantification is not silently replaced by Nat quantification. -/
def ExactUniversalDomains : Prop := ∀ (p : Formula), p.certified → ∀ i ν,
  ((translate (forallNat i p)).eval ν ↔ ∀ n : Nat, p.eval (Function.update ν i n)) ∧
  ((translate (forallPositive i p)).eval ν ↔ ∀ n : Nat, 0 < n → p.eval (Function.update ν i n))

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadFirstOrderTargets
