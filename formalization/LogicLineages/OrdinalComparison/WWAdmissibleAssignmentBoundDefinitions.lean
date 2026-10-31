module
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentDefinitions
public import LogicLineages.OrdinalComparison.WWLiteralSizeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AdmissibleAssignmentBound

/-- A uniform literal node bound for the actual box, including its scalar
policy-expanded tail. It uses only natural arithmetic and input size bounds. -/
def boxBound (n A B : Nat) : Nat := (n + 3) * (A + B + 2) + 2 * n + 3

/-- Uniform lambda/abstraction bound. n is level(X)+1; m is the input vector
level. This bounds syntax, not ordinal norm or a collapse value. -/
def abstractionBound (n m N : Nat) : Nat :=
  (2 ^ n * (m + 1) * 2 ^ N + m + 2) * (6 * 3 ^ N + N + 3)

/-- Explicit structural recursion on the actual original typed source. This
function inspects no policy, ordinal value or future partial-success oracle. -/
def sourceBound {Γ : List Ty} {τ : Ty} : OriginalTerm Γ τ → Nat
  | .var _ | .zeroC | .succC | .caseC _ => 1
  | .recC _ => 3
  | @Term.app _ _ _ σ _ f g => boxBound σ.level (sourceBound f) (sourceBound g)
  | @Term.lam _ _ _ σ τ body => abstractionBound (σ.level + 1) τ.level (sourceBound body)
  | .ranked s _ => nomatch s

end LogicLineages.OrdinalComparison.Source.AdmissibleAssignmentBound
