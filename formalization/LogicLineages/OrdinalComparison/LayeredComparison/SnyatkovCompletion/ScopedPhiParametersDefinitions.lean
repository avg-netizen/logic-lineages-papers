module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveParameterDecisionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiParameters
open CommonLayerSyntax

/-- A Phi application may depend on original free parameters only. The active
binder list retains duplicates and original names; no renaming is performed. -/
def termTest (bound : List Nat) : BaseTerm → Bool
  | .numeral _ | .variable _ => true
  | .add a b => termTest bound a && termTest bound b
  | .phi t => t.variables.all (fun i => !bound.contains i)

def test (bound : List Nat) : SourceFormula → Bool
  | .equal a b | .less a b => termTest bound a && termTest bound b
  | .negative p => test bound p
  | .conjunction p q => test bound p && test bound q
  | .existsNat i p => test (i :: bound) p

/-- Replace each entire original Phi application by its actual value in the
ambient parameter valuation. Its internal nested Phi applications are evaluated
as part of that value. Plain names, sums and all original binders remain. -/
def freezeTerm (ambient : Nat → Nat) : BaseTerm → BaseTerm
  | .numeral n => .numeral n
  | .variable i => .variable i
  | .add a b => .add (freezeTerm ambient a) (freezeTerm ambient b)
  | .phi t => .numeral ((BaseTerm.phi t).value ambient)

def freezeFormula (ambient : Nat → Nat) : SourceFormula → SourceFormula
  | .equal a b => .equal (freezeTerm ambient a) (freezeTerm ambient b)
  | .less a b => .less (freezeTerm ambient a) (freezeTerm ambient b)
  | .negative p => .negative (freezeFormula ambient p)
  | .conjunction p q => .conjunction (freezeFormula ambient p) (freezeFormula ambient q)
  | .existsNat i p => .existsNat i (freezeFormula ambient p)

def decide (values : List Nat) (p : SourceFormula) : Option Bool :=
  if test [] p then AdditiveParameterDecision.decide values
    (freezeFormula (PlainParameterDecision.valuation values) p)
  else none

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiParameters
