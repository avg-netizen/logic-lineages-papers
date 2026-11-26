module
public import LogicLineages.PersistentMarking.NumberedWindowScalarAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowRawClassSaturationTargets
open NumberedWindowClassAlgorithm (advance rounds members)
open NumberedWindowScalarAlgorithm (Settings admitted edge vertices)

/-- The actual original ordered lists, not sets or a replacement
closure. Duplicates and an absent seed are both in scope. -/
def ExactLiteralClassSaturation : Prop :=
  ∀ (step : Nat → Nat → Bool) (pool : List Nat) (seed : Nat),
    (∀ fuel, List.Sublist (rounds step pool seed fuel) pool) ∧
    (∀ fuel, List.Sublist (rounds step pool seed fuel) (rounds step pool seed (fuel+1))) ∧
    advance step pool (members step pool seed) = members step pool seed

/-- A successful original minimum, queried as a new seed with the
SAME literal pool and directed edge, is its own original minimum. -/
def ExactSamePoolLeastSelf : Prop :=
  ∀ (step : Nat → Nat → Bool) (pool : List Nat) (seed y : Nat),
    NumberedWindowClassAlgorithm.least step pool seed = some y →
    NumberedWindowClassAlgorithm.least step pool y = some y

/-- Actual raw admission propagates along the original rounds of a
successful original least, regardless of new-pool equality. -/
def ExactRawLeastResultAdmitted : Prop :=
  ∀ (s : Settings) (ctx : List Nat) (requested seed y : Nat),
    admitted s ctx requested seed = true →
    NumberedWindowScalarAlgorithm.least s ctx requested seed = some y →
    admitted s ctx requested y = true

/-- The still separate source-specific invariant on the actual edge
and original ordered cover list. No reflexivity or symmetry premise. -/
def EdgePreservesVertices (s : Settings) (ctx : List Nat) (requested : Nat) : Prop :=
  ∀ a b, edge s ctx requested a b = true → vertices s b = vertices s a

/-- On the actual raw least, identify the output's own original pool
and own least only after the actual edge/vertices condition is paid.
Seed admission is required for the admitted-output conjunct. -/
def ExactRawLeastClosureWithVertices : Prop :=
  ∀ (s : Settings) (ctx : List Nat) (requested : Nat),
    EdgePreservesVertices s ctx requested →
    ∀ seed y,
      admitted s ctx requested seed = true →
      NumberedWindowScalarAlgorithm.least s ctx requested seed = some y →
      vertices s y = vertices s seed ∧ admitted s ctx requested y = true ∧
        NumberedWindowScalarAlgorithm.least s ctx requested y = some y

end LogicLineages.PersistentMarking.NumberedWindowRawClassSaturationTargets
