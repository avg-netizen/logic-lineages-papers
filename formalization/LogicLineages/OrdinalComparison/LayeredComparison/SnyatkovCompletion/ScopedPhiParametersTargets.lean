module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiParametersDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiParametersTargets
open CommonLayerSyntax ScopedPhiParameters

def AdditiveTermOutput : Prop := ∀ (ambient : Nat → Nat) (t : BaseTerm),
  AdditiveSource.termTest (freezeTerm ambient t) = true

def AdditiveFormulaOutput : Prop := ∀ (ambient : Nat → Nat) (p : SourceFormula),
  AdditiveSource.test (freezeFormula ambient p) = true

/-- The current valuation may vary arbitrarily at active bound names, while
all outside coordinates agree with the one fixed ambient parameter valuation. -/
def ScopedTermMeaning : Prop := ∀ (bound : List Nat) (ambient current : Nat → Nat) (t : BaseTerm),
  termTest bound t = true →
  (∀ i : Nat, i ∉ bound → current i = ambient i) →
  (freezeTerm ambient t).value current = t.value current

def ScopedFormulaMeaning : Prop := ∀ (bound : List Nat) (ambient current : Nat → Nat) (p : SourceFormula),
  test bound p = true →
  (∀ i : Nat, i ∉ bound → current i = ambient i) →
  ((freezeFormula ambient p).eval current ↔ p.eval current)

def ExactDecisionDomain : Prop := ∀ (values : List Nat) (p : SourceFormula),
  (ScopedPhiParameters.decide values p).isSome = test [] p

def ActualDecision : Prop := ∀ (values : List Nat) (p : SourceFormula), test [] p = true → ∀ b : Bool,
  ScopedPhiParameters.decide values p = some b ↔
    (p.eval (PlainParameterDecision.valuation values) ↔ b = true)

/-- Exact binder-sensitive Phi boundary and an explicit rejected captured
application. A bound-dependent application is rejected even if later simplified. -/
def LiteralScopeBoundary : Prop :=
  (∀ (bound : List Nat) (t : BaseTerm), termTest bound (.phi t) = true ↔
    ∀ i ∈ t.variables, i ∉ bound) ∧
  (∀ (bound : List Nat) (i : Nat) (p : SourceFormula),
    test bound (.existsNat i p) = test (i :: bound) p) ∧
  (∀ i : Nat, test [] (.existsNat i (.equal (.phi (.variable i)) (.numeral 0))) = false)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiParametersTargets
