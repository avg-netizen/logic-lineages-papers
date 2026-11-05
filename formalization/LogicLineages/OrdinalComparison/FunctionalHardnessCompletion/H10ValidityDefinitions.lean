module
public import LogicLineages.ComputabilityKnowledge.PolynomialCircuit
public import Mathlib.Computability.RE
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Validity
open LogicLineages.ComputabilityKnowledge.PolynomialCircuit

/-- Check every original variable occurrence against the original input arity.
Occurrences are checked even when their coefficient is zero. -/
def variablesValid (n : Nat) (vs : List Nat) : Bool :=
  vs.all (fun i => decide (i < n))

def termsValid (n : Nat) (ms : Monomials) : Bool :=
  ms.all (fun m => variablesValid n m.2)

/-- Validate the original polynomial codec before any domain shift or circuit
compilation. Parse failures and out-of-range original input indices both fail;
a compiled auxiliary gate must never mask an invalid original variable. -/
def validInput (xs : List Nat) : Bool :=
  (LogicLineages.ComputabilityKnowledge.PolynomialCircuit.decode xs).any
    (fun p => termsValid p.inputCount p.monomials)

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Validity
