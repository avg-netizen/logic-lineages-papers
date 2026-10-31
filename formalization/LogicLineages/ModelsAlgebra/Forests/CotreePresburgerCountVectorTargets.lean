module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCountVectorDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCountVector.Targets
open CotreePresburgerPullback

def CountsExact : Prop :=
  ∀ (Q : Type) [Fintype Q] [LinearOrder Q] (v : Q → Nat),
    wordCounts (realizeCounts v) = v

def LengthExact : Prop :=
  ∀ (Q : Type) [Fintype Q] [LinearOrder Q] (v : Q → Nat),
    (realizeCounts v).length = ∑ q, v q

def MembershipExact : Prop :=
  ∀ (Q : Type) [Fintype Q] [LinearOrder Q] (v : Q → Nat) q,
    q ∈ realizeCounts v ↔ 0 < v q

/-- A multiplicity vector of total at least two supplies actual finite child
occurrences, not an opaque realization assumption. -/
def ChildrenExact : Prop :=
  ∀ (Q : Type) [Fintype Q] [LinearOrder Q] (v : Q → Nat),
    2 ≤ ∑ q, v q → ∃ n, ∃ children : Fin (n + 2) → Q,
      List.ofFn children = realizeCounts v

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCountVector.Targets
