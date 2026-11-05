module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedFirstOrderDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedFirstOrderTargets
open BalancedFirstOrder

/-- Original free-name positivity survives binding, including repeated names and
shadowing, without constraining any unrelated coordinate or old binder value. -/
def BoundEnvironment : Prop := ∀ (p : Formula) i (ν : Nat → Nat) n, 0 < n →
  positive ν (.existsPositive i p) → positive (Function.update ν i n) p

/-- Exact truth at the original positive source domain, with arbitrary Boolean
structure and positive-binder alternation and EACH atom's own whole certificate. -/
def ActualSourceTranslation : Prop := ∀ p : Formula, p.certified → ∀ ν,
  positive ν p → ((translate p).eval ν ↔ p.eval ν)

/-- Exact free-variable sets, without semantic validity or positivity premises. -/
def ExactFreeVariables : Prop := ∀ (p : Formula) i,
  i ∈ (translate p).variables ↔ i ∈ p.variables

def LiteralCodeCalibration : Prop := ∀ p : Formula,
  Code.translate p.encode = (translate p).encode

def ActualSourceCode : Prop := ∀ p : Formula, p.certified → ∀ ν, positive ν p →
  ((SourceFormulaCodec.decode (Code.translate p.encode)).eval ν ↔ p.eval ν)

/-- Computation emits syntax on EVERY raw code, including malformed payloads.
It is not a procedure deciding arbitrary quantified BASE truth. -/
def ActualNumericProgram : Prop := Computable Code.translate

/-- Universal positive quantification is the exact dual, not Nat universality;
positivity of the body's bound name is supplied by the quantifier itself. -/
def ExactUniversalDomain : Prop := ∀ (p : Formula), p.certified → ∀ i ν,
  positive ν (.existsPositive i p) →
  ((translate (forallPositive i p)).eval ν ↔ ∀ n : Nat, 0 < n → p.eval (Function.update ν i n))

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedFirstOrderTargets
