module
public import LogicLineages.OrdinalComparison.EncodedDescentDefinitions
public import LogicLineages.OrdinalComparison.EncodedSuffixKernelDefinitions
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.Definitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalScheduled

/-- One literal original replacement: discard the finite tail and maximize
under the independently time-indexed SOURCE budget. The step does not replace
that budget by a function of the current norm. Raw malformed behavior is the
existing total rawSplit/encodedMaximum behavior. Source meaning is asserted
only before the first finite state. -/
def step (c t index state : Nat) : Nat :=
  encodedMaximumPredecessor (rawSplitCode state).unpair.1
    (KernelSourceCompletion.sourceBudget c t index)

def advance (c t : Nat) (state : Nat × Nat) : Nat × Nat :=
  (state.1 + 1, step c t state.1 state.2)

/-- The explicit index starts at zero and advances once per replacement.
The first budget is consequently Phi(t)-c, exactly sourceBudget c t 0. -/
def run (c t initial k : Nat) : Nat :=
  ((advance c t)^[k] (0, initial)).2

def search (c t initial : Nat) : Part Nat :=
  Nat.rfind (fun k => Part.some (encodedFiniteTest (run c t initial k)))

/-- A real partial search; totality is a mathematical obligation. Malformed
normal-form inputs return zero immediately rather than entering that search. -/
def countPartial (c t initial : Nat) : Part Nat :=
  if rawNormalCode initial = 1 then search c t initial else Part.some 0

noncomputable def countValue (c t initial : Nat) : Nat := by
  classical
  exact (countPartial c t initial).getOrElse 0

/-- The unpadded principal omega^d, with no compensated finite suffix. -/
def initial (d : Nat) : Nat := encodedNodeCode (encodedNatNote d) 0 0

noncomputable def sourceCount (d c t : Nat) : Nat := countValue c t (initial d)

end LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalScheduled
