module
public import LogicLineages.PermittedControl.SortedHighFieldProjectionTargets
import LogicLineages.PermittedControl.StableSortedHighFieldGuardProof
import LogicLineages.PermittedControl.PreparedParameterActualProof
import LogicLineages.PermittedControl.PreparedParameterOutputProof

@[expose] public section
namespace LogicLineages.PermittedControl.StableSortedHighField
open OrdinalComparison FieldComparison PreparedProjection

theorem actualSortedHighProjection : ActualSortedHighProjection := by
  intro f B selected F G properF properG ρ lowRank highRank wanted rankOrder bound
  let packet := guardedPacket F G lowRank wanted
  obtain ⟨shape,readings,meaning⟩ :=
    actualGuardedPacket f B selected F G properF properG ρ lowRank highRank wanted rankOrder bound
  have output := preparedProjectionSyntax packet.1 packet.2 shape
  have shapeOut : PreparedInput packet.1 (projection F G lowRank wanted) :=
    ⟨output.2.1,fun i used => (output.2.2.2 i used).2⟩
  have removed : 0 ∉ (projection F G lowRank wanted).variables :=
    fun used => ((output.2.2.1 0).mp used).1 rfl
  refine ⟨shapeOut,removed,readings,?_⟩
  intro ν tied
  have keeps (z : Nat) :
      PreparedTableTied f highRank ρ packet.1 (Function.update ν 0 z) := by
    intro j used
    have nonzero : j + 1 ≠ 0 := by omega
    simpa only [Function.update_of_ne nonzero] using tied j used
  change (eliminatePreparedFormula packet.2).eval ν ↔
    ∃ z : Nat, ρ lowRank < z ∧ actualOutcome f F G (ρ lowRank) z wanted
  rw [preparedProjectionActual packet.1 packet.2 shape]
  constructor
  · rintro ⟨z,holds⟩
    have actual := (meaning (Function.update ν 0 z) (keeps z)).mp holds
    exact ⟨z,by simpa only [Function.update_self] using actual⟩
  · rintro ⟨z,ordered,actual⟩
    refine ⟨z,(meaning (Function.update ν 0 z) (keeps z)).mpr ?_⟩
    simpa only [Function.update_self] using And.intro ordered actual

end LogicLineages.PermittedControl.StableSortedHighField
