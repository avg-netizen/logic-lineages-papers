module
public import LogicLineages.OrdinalComparison.CollectedNormalizeDefinitions
public import LogicLineages.OrdinalComparison.PositiveInputSupportDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Reinterpret the same literal positive tree in a supplied unary-head
algebra. The actual source is the specialization H=actualProfileHead. -/
def interpretedPositiveEval (H : NONote → Nat → Nat) : FixedLimitPositiveExpr → Nat → Nat
  | .constant c, _ => c
  | .input, x => x
  | .add E F, x => interpretedPositiveEval H E x + interpretedPositiveEval H F x
  | .head rho E, x => H rho (interpretedPositiveEval H E x)

mutual
  def interpretedCollectedEval (H : NONote → Nat → Nat) : CollectedPositiveNF → Nat → Nat
    | .mk c b tags, x => c+b*x+interpretedCollectedTagsEval H tags x
  def interpretedCollectedTagsEval (H : NONote → Nat → Nat) : CollectedPositiveTags → Nat → Nat
    | .nil, _ => 0
    | .cons rho A a rest, x => a*H rho (interpretedCollectedEval H A x) +
        interpretedCollectedTagsEval H rest x
end

/-- The normalizer evaluates closed calls in the actual ordinal model.
A replacement algebra must agree at those literal closed-call heads.
This recursive condition will be PAID for fresh-variable embeddings, rather
than introduced as a premise of the eventual source equality theorem. -/
def PositiveClosedHeadAgreement (H : NONote → Nat → Nat) : FixedLimitPositiveExpr → Prop
  | .constant _ => True
  | .input => True
  | .add E F => PositiveClosedHeadAgreement H E ∧ PositiveClosedHeadAgreement H F
  | .head rho E => PositiveClosedHeadAgreement H E ∧
      (positiveExprHasInput E=false → ∀ z : Nat, H rho z=actualProfileHead rho z)

def positiveHeadsSatisfy (P : NONote → Prop) : FixedLimitPositiveExpr → Prop
  | .constant _ => True
  | .input => True
  | .add E F => positiveHeadsSatisfy P E ∧ positiveHeadsSatisfy P F
  | .head rho E => P rho ∧ positiveHeadsSatisfy P E

mutual
  def collectedHeadsSatisfy (P : NONote → Prop) : CollectedPositiveNF → Prop
    | .mk _ _ tags => collectedTagHeadsSatisfy P tags
  def collectedTagHeadsSatisfy (P : NONote → Prop) : CollectedPositiveTags → Prop
    | .nil => True
    | .cons rho A _ rest => P rho ∧ collectedHeadsSatisfy P A ∧ collectedTagHeadsSatisfy P rest
end

end LogicLineages.OrdinalComparison
