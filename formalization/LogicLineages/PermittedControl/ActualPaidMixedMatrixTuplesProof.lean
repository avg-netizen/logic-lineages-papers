module
public import LogicLineages.PermittedControl.ActualPaidMixedMatrixTuplesTargets
import LogicLineages.PermittedControl.ActualPaidMixedMatrixTuplesRowProof
import LogicLineages.PermittedControl.ActualSignedRouteCartesianChoiceProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualPaidMixedMatrixTuples
open ActualPreparedSlotAppend (Packet)
open ActualSelectedSignedRoutePacket (Shape)
open ActualSignedRouteCartesian (tuplePacket exactCartesianPacketEval)

theorem exactMixedMatrixMinimum : ExactMixedMatrixMinimum := by
  intro B r top baseline rows z
  induction rows with
  | nil =>
    exact ⟨fun _ row used => False.elim (List.not_mem_nil used),fun _ => Nat.zero_le _⟩
  | cons row rows ih =>
    change max (rowMinimum B r top baseline row) (matrixMinimum B r top baseline rows) ≤ z ↔ _
    constructor
    · intro above other member
      rcases List.mem_cons.mp member with eq | tail
      · subst other
        exact (le_max_left _ _).trans above
      · exact (ih.mp ((le_max_right _ _).trans above)) other tail
    · intro each
      exact max_le (each row List.mem_cons_self)
        (ih.mpr (fun q used => each q (List.mem_cons_of_mem _ used)))

private theorem allShape (f baseline : Nat → Nat) (r top z : Nat) (rows : List MixedRow) :
    ∀ row ∈ rows.map (alternatives r top), ∀ p ∈ row, Shape p := by
  intro pack used
  obtain ⟨source,_,rfl⟩ := List.mem_map.mp used
  exact alternativesShape f baseline r top z source

theorem exactMixedTupleShape : ExactMixedTupleShape := by
  intro r top rows
  exact (exactCartesianPacketEval (fun _ => 0) (fun _ => 0) top 0
    (rows.map (alternatives r top)) (allShape (fun _ => 0) (fun _ => 0) r top 0 rows)).1

theorem exactPaidMixedMatrixTuples : ExactPaidMixedMatrixTuples := by
  intro f B selected r top baseline rows setup z minimum
  have rowExact (row : MixedRow) (used : row ∈ rows) :=
    exactPaidMixedRow f B selected r top baseline row (setup row used) z
      ((exactMixedMatrixMinimum B r top baseline rows z).mp minimum row used)
  have cart := (exactCartesianPacketEval f baseline top z (rows.map (alternatives r top))
    (allShape f baseline r top z rows)).2
  refine Iff.trans ?_ cart.symm
  constructor
  · intro truth a used
    obtain ⟨row,member,rfl⟩ := List.mem_map.mp used
    exact (rowExact row member).mp (truth row member)
  · intro all row used
    exact (rowExact row used).mpr (all (alternatives r top row) (List.mem_map.mpr ⟨row,used,rfl⟩))

end LogicLineages.PermittedControl.ActualPaidMixedMatrixTuples
