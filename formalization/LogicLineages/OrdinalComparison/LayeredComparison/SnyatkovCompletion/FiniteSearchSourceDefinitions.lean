module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchSource
open CommonLayerSyntax

/-- Boolean and genuinely finite-bounded closure of the checked unbounded
additive fragment with free-parameter Phi. Test each subformula in its current
ambient environment, not in a discarded outer valuation. -/
def test (p : SourceFormula) : Bool :=
  ScopedPhiParameters.test [] p || match p with
  | .negative q => test q
  | .conjunction q r => test q && test r
  | .existsNat i q => (BoundedSource.guard i q).isSome && test q
  | _ => false

def answer (values : List Nat) (p : SourceFormula) : Bool :=
  if ScopedPhiParameters.test [] p then (ScopedPhiParameters.decide values p).getD false
  else match p with
  | .negative q => !answer values q
  | .conjunction q r => answer values q && answer values r
  | .existsNat i q => match BoundedSource.guard i q with
      | none => false
      | some t => (List.range (t.value (PlainParameterDecision.valuation values))).any (fun n =>
          answer (BoundedSourcePrograms.Code.update values i n) q)
  | _ => false

def decide (values : List Nat) (p : SourceFormula) : Option Bool :=
  if test p then some (answer values p) else none

/-- A bounded nonlinear outer name supplies a parameter to a genuinely
unbounded additive inner quantifier. Original distinct names are not renamed. -/
def boundedOuter (i j : Nat) (bound : BaseTerm) : SourceFormula :=
  .existsNat i (.conjunction (.less (.variable i) bound)
    (.existsNat j (.equal (.variable j) (.phi (.variable i)))))

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchSource
