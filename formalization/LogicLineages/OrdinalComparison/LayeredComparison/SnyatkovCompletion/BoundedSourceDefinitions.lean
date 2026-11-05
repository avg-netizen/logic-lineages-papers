module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiParametersDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSource
open CommonLayerSyntax

/-- Recognize an original leading bound conjunct. The bound may use arbitrary
nested Phi and other surrounding variables, but not the name being bound here. -/
def guard (i : Nat) : SourceFormula → Option BaseTerm
  | .conjunction (.less (.variable j) t) _ =>
      if i = j ∧ i ∉ t.variables then some t else none
  | _ => none

def test : SourceFormula → Bool
  | .equal _ _ | .less _ _ => true
  | .negative p => test p
  | .conjunction p q => test p && test q
  | .existsNat i p => (guard i p).isSome && test p

/-- Search the actual finite initial segment and retain the entire original
body, including its bound conjunct. Updates use the original name, so shadowing
and bounds depending on outer quantified names have their usual semantics. -/
def answer (ν : Nat → Nat) : SourceFormula → Bool
  | .equal a b => decide (a.value ν = b.value ν)
  | .less a b => decide (a.value ν < b.value ν)
  | .negative p => !answer ν p
  | .conjunction p q => answer ν p && answer ν q
  | .existsNat i p => match guard i p with
      | none => false
      | some t => (List.range (t.value ν)).any (fun n => answer (Function.update ν i n) p)

def decide (values : List Nat) (p : SourceFormula) : Option Bool :=
  if test p then some (answer (PlainParameterDecision.valuation values) p) else none

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSource
