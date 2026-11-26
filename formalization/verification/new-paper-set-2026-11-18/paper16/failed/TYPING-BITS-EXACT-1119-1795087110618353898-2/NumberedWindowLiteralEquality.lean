import LogicLineages.PersistentMarking.NumberedWindowSyntax

namespace LogicLineages.PersistentMarking.NumberedWindowLiteralEquality
open NumberedWindowSyntax

/- Actual structural identity of the numerical syntax. This does not use
head precedence classes, permute arguments, erase annotations, or
normalize beta. Both typed free-name fields are compared. -/
mutual
def termEq : NTerm → NTerm → Bool
  | .free σ x, .free τ y | .bound σ x, .bound τ y =>
    decide (σ = τ) && decide (x = y)
  | .lam σ Q, .lam τ R => decide (σ = τ) && termEq Q R
  | .bottom σ, .bottom τ => decide (σ = τ)
  | .ordinary f bs, .ordinary g cs => decide (f = g) && argsEq bs cs
  | .numbered f σ k bs es, .numbered g τ j cs ds =>
    decide (f = g) && decide (σ = τ) && decide (k = j) && argsEq bs cs && argsEq es ds
  | .auxApp σ τ Q A, .auxApp ρ υ R B =>
    decide (σ = ρ) && decide (τ = υ) && termEq Q R && termEq A B
  | _, _ => false

def argsEq : NArgs → NArgs → Bool
  | .nil, .nil => true
  | .cons Q qs, .cons R rs => termEq Q R && argsEq qs rs
  | _, _ => false
end

end LogicLineages.PersistentMarking.NumberedWindowLiteralEquality
