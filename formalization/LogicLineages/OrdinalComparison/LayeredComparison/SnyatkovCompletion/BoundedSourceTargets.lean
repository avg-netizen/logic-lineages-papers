module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceTargets
open CommonLayerSyntax BoundedSource

def LiteralGuard : Prop := ∀ (i : Nat) (p : SourceFormula) (t : BaseTerm),
  guard i p = some t ↔ ∃ q, p = .conjunction (.less (.variable i) t) q ∧ i ∉ t.variables

def ExactGuardInvariance : Prop := ∀ (i : Nat) (p : SourceFormula) (t : BaseTerm),
  guard i p = some t → ∀ (ν : Nat → Nat) (n : Nat),
    t.value (Function.update ν i n) = t.value ν ∧
    (p.eval (Function.update ν i n) → n < t.value ν)

def ExactFiniteSearch : Prop := ∀ (i : Nat) (p : SourceFormula) (t : BaseTerm),
  guard i p = some t → ∀ (ν : Nat → Nat),
    answer ν (.existsNat i p) = true ↔
      ∃ n < t.value ν, answer (Function.update ν i n) p = true

def ActualTruth : Prop := ∀ (p : SourceFormula), test p = true → ∀ (ν : Nat → Nat),
  answer ν p = true ↔ p.eval ν

def ActualDecision : Prop := ∀ (values : List Nat) (p : SourceFormula),
  (BoundedSource.decide values p).isSome = test p ∧
  (test p = true → ∀ (b : Bool), BoundedSource.decide values p = some b ↔
    (p.eval (PlainParameterDecision.valuation values) ↔ b = true))

/-- The literal negated bounded existential is the actual finite universal,
including empty bounds. No unrestricted universal quantifier is asserted. -/
def ActualBoundedUniversal : Prop := ∀ (i : Nat) (t : BaseTerm) (p : SourceFormula),
  i ∉ t.variables → test p = true → ∀ (ν : Nat → Nat),
    answer ν (.negative (.existsNat i (.conjunction (.less (.variable i) t) (.negative p)))) = true ↔
      ∀ n < t.value ν, p.eval (Function.update ν i n)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceTargets
