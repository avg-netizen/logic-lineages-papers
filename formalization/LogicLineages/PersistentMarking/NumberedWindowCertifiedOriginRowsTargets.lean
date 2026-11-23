module
public import LogicLineages.PersistentMarking.NumberedWindowDirectAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginRowsTargets
open NumberedWindowDirectAlgorithm (Entry)

/-- The per-row Boolean check of the literal direct replacement, unpacked
on the same target, dominator, and certificate fields of each row. -/
def RowFit (positive : Nat → Nat → Nat → Bool) (removed : List Nat)
    (rows : List Entry) : Prop :=
  ∀ e ∈ rows, e.2.1 ∈ removed ∧ positive e.2.1 e.2.2 e.1 = true

def ExactOriginRowAssignment : Prop :=
  ∀ (positive : Nat → Nat → Nat → Bool)
      (removed removedLeft removedRight : List Nat) (rows : List Entry),
    removed.Perm (removedLeft ++ removedRight) →
    RowFit positive removed rows →
    ∃ rowsLeft rowsRight,
      rows.Perm (rowsLeft ++ rowsRight) ∧
      RowFit positive removedLeft rowsLeft ∧ RowFit positive removedRight rowsRight

def ExactOriginTargetRecombination : Prop :=
  ∀ (target kept keptLeft keptRight : List Nat) (rows rowsLeft rowsRight : List Entry),
    target.Perm (kept ++ rows.map Prod.fst) →
    kept.Perm (keptLeft ++ keptRight) →
    rows.Perm (rowsLeft ++ rowsRight) →
    target.Perm ((keptLeft ++ rowsLeft.map Prod.fst) ++ (keptRight ++ rowsRight.map Prod.fst))

end LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginRowsTargets
