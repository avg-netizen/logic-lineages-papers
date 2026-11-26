module

public import Init

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowFiniteSaturation
universe u

/-- Grow inside the same literal carrier list. Original copies of already
reached values are retained via literal equality; a fresh value needs an
actual single edge from some previously reached value. -/
def advance {α : Type u} (vertices : List α) (same edge : α → α → Bool)
    (seen : List α) : List α :=
  vertices.filter (fun v => seen.any (fun w => same w v || edge w v))

def rounds {α : Type u} (vertices : List α) (same edge : α → α → Bool) (seed : α) :
    Nat → List α
  | 0 => vertices.filter (same seed)
  | n+1 => advance vertices same edge (rounds vertices same edge seed n)

def saturate {α : Type u} (vertices : List α) (same edge : α → α → Bool) (seed : α) :
    List α :=
  rounds vertices same edge seed vertices.length

/-- Finite paths in the indicated finite graph, defined independently of
the search iterations and length bound. A path has a real stored edge at
each successor. The zero path requires the actual seed to belong. -/
inductive GraphReach {α : Type u} (vertices : List α) (edge : α → α → Bool)
    (seed : α) : α → Prop where
  | start : seed ∈ vertices → GraphReach vertices edge seed seed
  | next : GraphReach vertices edge seed w → v ∈ vertices → edge w v = true →
      GraphReach vertices edge seed v

def EqualityTest {α : Type u} (same : α → α → Bool) : Prop :=
  ∀ x y, same x y = true ↔ x = y

end LogicLineages.PersistentMarking.NumberedWindowFiniteSaturation
