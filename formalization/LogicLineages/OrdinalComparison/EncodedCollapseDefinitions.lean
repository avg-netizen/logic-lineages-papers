module
public import LogicLineages.OrdinalComparison.EncodedDescentDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section

/-! A concrete partial recursive-program candidate for source closed collapse.
Least search finds the first finite state and returns its finite value plus
the number of replacements. Nonnormal raw inputs return zero immediately.
The total-value wrapper uses zero only if the partial program is undefined;
totality, actual computability and agreement with actualCollapse are independent
targets, not an assumed termination field or a consequence of this wrapper.
-/

namespace LogicLineages.OrdinalComparison

def encodedTerminalSearch (n : Nat) : Part Nat :=
  Nat.rfind (fun k => Part.some (encodedFiniteTest (encodedStateAfter n k)))

def encodedCollapsePartial (n : Nat) : Part Nat :=
  if rawNormalCode n = 1 then
    (encodedTerminalSearch n).map (fun k => encodedFiniteValue (encodedStateAfter n k) + k)
  else Part.some 0

noncomputable def encodedCollapseValue (n : Nat) : Nat := by
  classical
  exact (encodedCollapsePartial n).getOrElse 0

end LogicLineages.OrdinalComparison
