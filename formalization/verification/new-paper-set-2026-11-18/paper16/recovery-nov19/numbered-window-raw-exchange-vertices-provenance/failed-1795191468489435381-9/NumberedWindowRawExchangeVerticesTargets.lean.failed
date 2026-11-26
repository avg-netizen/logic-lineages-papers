module
public import LogicLineages.PersistentMarking.NumberedWindowScalarAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesTargets
open NumberedWindowPairAlgorithm (pair decode)
open NumberedWindowFieldAlgorithm (unpack unpackNode)
open NumberedWindowCoverBoundsAlgorithm (Measure bounds)
open NumberedWindowExchangeAtoms (HeadPairs bag)
open NumberedWindowExchangeAlgorithm (bits)
open NumberedWindowScalarAlgorithm (Settings edge vertices)

/-- Successful raw parser branches only, with literal polynomial
pair inversion and actual numerically smaller decoded fields. No
decoder completeness or PR shadow codec premise. -/
def ExactOriginalRawFieldBounds : Prop :=
  (∀ n a b, decode n = some (a,b) → pair a b = n ∧ a ≤ n ∧ b ≤ n) ∧
  (∀ a b c d, pair a b = pair c d → a = c ∧ b = d) ∧
  (∀ n xs, unpack n = some xs → ∀ v ∈ xs, v < n) ∧
  (∀ n tag xs, unpackNode n = some (tag,xs) → 0 < n ∧ ∀ v ∈ xs, v < n)

/-- The first coordinate includes one node for each actual argument
list cell. The second is the maximum raw variable/mark numeral,
using the actual original term bounds at each original field. -/
def argsFold : List Nat → Measure
  | [] => (0,0)
  | x::xs =>
      let t := (bounds x).1
      let tail := argsFold xs
      (t.1 + 1 + tail.1,max t.2 tail.2)

/-- Relate the actual successful raw unpack, including duplicates,
to the same original args bound table. An actual approved bag
permutation then preserves that bound, without sorting the list. -/
def ExactOriginalRawArgsBounds : Prop :=
  (∀ n xs, unpack n = some xs → (bounds n).2 = argsFold xs) ∧
  (∀ a b, bag a b = true → (bounds a).2 = (bounds b).2)

/-- Both guarded term and guarded ordered-args exchange of the actual
raw table preserve the corresponding original node/numeral bound. -/
def ExactOriginalGuardedExchangeBounds : Prop :=
  ∀ (hp : HeadPairs) a b,
    ((bits hp a b).1 = true → (bounds a).1 = (bounds b).1) ∧
    ((bits hp a b).2 = true → (bounds a).2 = (bounds b).2)

/-- The same actual directed scalar edge preserves the literal
ordered vertices list (including duplicates, not just membership).
This pays the separate same-pool condition, not application closure. -/
def ExactOriginalGuardedEdgeVertices : Prop :=
  ∀ (s : Settings) (ctx : List Nat) (requested a b : Nat),
    edge s ctx requested a b = true → vertices s b = vertices s a

end LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesTargets
