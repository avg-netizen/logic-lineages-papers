module
public import LogicLineages.PermittedControl.StableSortedHighFieldTargets
import LogicLineages.PermittedControl.StableSortedHighFieldPacketProof
import LogicLineages.PermittedControl.StableSortedHighFieldValuesProof

@[expose] public section
namespace LogicLineages.PermittedControl.StableSortedHighField
open OrdinalComparison FieldComparison PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion

private theorem originalLookup (table : List LowerOperand) (lowRank j : Nat)
    (used : j < table.length) {larger : j < (table ++ [LowerOperand.coordinate lowRank]).length} :
    (table ++ [LowerOperand.coordinate lowRank]).get ⟨j,larger⟩ = table.get ⟨j,used⟩ :=
  List.getElem_append_left used

private theorem appendedLookup (table : List LowerOperand) (lowRank : Nat) :
    (table ++ [LowerOperand.coordinate lowRank]).get ⟨table.length,by simp⟩ =
      LowerOperand.coordinate lowRank := by
  change (table ++ [LowerOperand.coordinate lowRank])[table.length] = _
  rw [List.getElem_append_right (le_refl table.length)]
  simp

private theorem keepLowerReadings (f ρ : Nat → Nat) (lowRank highRank : Nat)
    (table : List LowerOperand) (ν : Nat → Nat)
    (tied : PreparedTableTied f highRank ρ (table ++ [LowerOperand.coordinate lowRank]) ν) :
    PreparedTableTied f highRank ρ table ν ∧ ν (table.length+1) = ρ lowRank := by
  constructor
  · intro j used
    have enlarged : j < (table ++ [LowerOperand.coordinate lowRank]).length := by
      simpa using Nat.lt_succ_of_lt used
    have original := tied j enlarged
    simpa only [originalLookup table lowRank j used] using original
  · have original := (tied table.length (by simp)).2
    rw [appendedLookup] at original
    exact original

private theorem addLowerReading (f ρ : Nat → Nat) (lowRank highRank : Nat)
    (rankOrder : lowRank < highRank) (table : List LowerOperand) (ν : Nat → Nat)
    (tied : PreparedTableTied f highRank ρ table ν)
    (reads : ∀ (j : Nat) (used : j < table.length),
      lowerOperandRead f ρ (table.get ⟨j,used⟩) = some (some (ν (j+1)))) :
    let enlarged := table ++ [LowerOperand.coordinate lowRank]
    ∃ μ : Nat → Nat, PreparedTableTied f highRank ρ enlarged μ ∧
      ∀ (j : Nat) (used : j < enlarged.length),
        lowerOperandRead f ρ (enlarged.get ⟨j,used⟩) = some (some (μ (j+1))) := by
  let μ := Function.update ν (table.length+1) (ρ lowRank)
  have checked (j : Nat) (used : j < (table ++ [LowerOperand.coordinate lowRank]).length) :
      let op := (table ++ [LowerOperand.coordinate lowRank]).get ⟨j,used⟩
      op.rank < highRank ∧ LowerOperandActual f ρ op (μ (j+1)) ∧
        lowerOperandRead f ρ op = some (some (μ (j+1))) := by
    dsimp only
    by_cases original : j < table.length
    · rw [originalLookup table lowRank j original]
      have kept : μ (j+1) = ν (j+1) :=
        Function.update_of_ne (by omega) (ρ lowRank) ν
      rw [kept]
      exact ⟨(tied j original).1,(tied j original).2,reads j original⟩
    · have size : j < table.length+1 := by simpa using used
      have last : j = table.length := by omega
      subst j
      rw [appendedLookup]
      exact ⟨rankOrder,by simp [μ,LowerOperandActual],by simp [μ,lowerOperandRead]⟩
  exact ⟨μ,fun j used => ⟨(checked j used).1,(checked j used).2.1⟩,
    fun j used => (checked j used).2.2⟩

theorem actualGuardedPacket : ActualGuardedPacket := by
  intro f B selected F G properF properG ρ lowRank highRank wanted rankOrder bound
  let base := basePacket F G lowRank wanted
  have shape := (basePacketExact F G lowRank highRank wanted rankOrder).2
  obtain ⟨ν,tied,reads⟩ :=
    baseActualReads f B selected F G properF properG ρ lowRank highRank wanted rankOrder bound
  refine ⟨appendOrderShape base.1 base.2 lowRank shape,
    addLowerReading f ρ lowRank highRank rankOrder base.1 ν tied reads,?_⟩
  intro assignment joined
  obtain ⟨original,lower⟩ := keepLowerReadings f ρ lowRank highRank base.1 assignment joined
  change ((orderGuard (base.1.length+1)).eval assignment ∧ base.2.eval assignment) ↔
    ρ lowRank < assignment 0 ∧ actualOutcome f F G (ρ lowRank) (assignment 0) wanted
  rw [orderGuardEval,lower]
  constructor
  · rintro ⟨ordered,actual⟩
    exact ⟨ordered,(baseMeaning f B selected F G properF properG ρ lowRank highRank wanted bound
      assignment original ordered).mp actual⟩
  · rintro ⟨ordered,actual⟩
    exact ⟨ordered,(baseMeaning f B selected F G properF properG ρ lowRank highRank wanted bound
      assignment original ordered).mpr actual⟩

end LogicLineages.PermittedControl.StableSortedHighField
