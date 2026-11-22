module
public import LogicLineages.PermittedControl.ActualCountLeadingErrorTargets
import LogicLineages.PermittedControl.CountTransferCoreProof
import LogicLineages.PermittedControl.EntryBasicsProof
import LogicLineages.PermittedControl.SelectedNonlinearImageBoundsGrowthProof
import LogicLineages.OrdinalComparison.OrdinalRepresentationSound

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCountLeadingError
open OrdinalComparison FieldComparison PreparedProjection
open Targets (countCoreConstant)

theorem exactActualCountLeadingError : ExactActualCountLeadingError := by
  intro f B selected ρ rank lam mu value proper tail actual
  let x := ρ rank
  let A := countInitial lam.1.repr x
  let η := mu.1.repr + Ordinal.omega0 ^ (2 : Ordinal.{0})
  let κ := countCoreConstant mu.1.repr
  obtain ⟨limit,targetLimit,below,long⟩ := proper
  obtain ⟨prefixBound,i,k,first,full,orbit,equation⟩ :=
    countCore f B selected lam.1.repr mu.1.repr x (normalRepresentationSound lam)
      limit targetLimit below long tail
  have actualFirst : FirstEntry f A mu.1.repr value := actual.2
  have same : value = k := firstEntry_unique f A mu.1.repr value k actualFirst full
  let q := entryNormAt f A i
  have indexed : x + i ≤ q := by
    change x + i ≤ entryNormAt f A i
    rw [orbit]
    exact SelectedNonlinearImageBounds.orbitGrowth f B selected x i
  have dominates : f x ≤ f q :=
    (selected_threshold_admissible f B selected).1.monotone ((Nat.le_add_right _ _).trans indexed)
  have ownLog : q ≤ Nat.log2 (f q) :=
    SelectedNonlinearImageBounds.rawCoordinateLogBound f B selected q (f q) le_rfl
  have doubled : 2 * (value : Int) = (f q : Int) + 2 * ((i : Int) + κ) := by
    rw [same]
    change 2 * (k : Int) = (f (entryNormAt f A i) : Int) +
      2 * ((i : Int) + countCoreConstant mu.1.repr)
    omega
  have triangle : ((i : Int) + κ).natAbs ≤ i + κ.natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_add_le (i : Int) κ
  have useBound (D : Nat) (large : f q ≤ D) :
      ((i : Int) + κ).natAbs ≤ Nat.log2 D + κ.natAbs := by
    have log := SelectedNonlinearImageBounds.rawCoordinateLogBound f B selected q D large
    have index : i ≤ Nat.log2 D := by omega
    exact triangle.trans (Nat.add_le_add_right index _)
  exact ⟨prefixBound,i,first,orbit,indexed,dominates,ownLog,doubled,useBound (f q) le_rfl,useBound⟩

end LogicLineages.PermittedControl.ActualCountLeadingError
