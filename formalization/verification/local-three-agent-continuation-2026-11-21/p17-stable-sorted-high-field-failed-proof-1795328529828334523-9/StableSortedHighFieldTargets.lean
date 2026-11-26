module
public import LogicLineages.PermittedControl.HighFieldPreparedActualTargets

@[expose] public section
namespace LogicLineages.PermittedControl.StableSortedHighField
open OrdinalComparison FieldComparison
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection HighFieldPreparedPacket

abbrev Packet := List LowerOperand × NormalForm.Formula

/-- The original sorted descriptor supplies one fixed typed packet,
before the greater raw coordinate is assigned its value. -/
def basePacket (F G : ValueField) (lowRank wanted : Nat) : Packet :=
  if wanted ≤ 2 then
    match distinctForm (normalizeShortField F) (normalizeShortField G) with
    | .const answer => ([],constantFormula 0 answer wanted)
    | .linear sign H => ([.ordinary lowRank H],InverseComparisonPreparedRows.emitFormula sign wanted)
  else ([],.falsity)

/-- The real strict-order constraint is the signed row z - x - 1 ≥ 0. -/
def orderGuard (lowerName : Nat) : NormalForm.Formula :=
  .atom (.nonnegative (-1,[(1,.variable 0),(-1,.variable lowerName)]))

/-- Keep the base requests and append the original raw lower input.
Its own slot is used by the explicit strict-order guard. -/
def guardedPacket (F G : ValueField) (lowRank wanted : Nat) : Packet :=
  let base := basePacket F G lowRank wanted
  (base.1 ++ [.coordinate lowRank],.conjunction (orderGuard (base.1.length+1)) base.2)

def actualOutcome (f : Nat → Nat) (F G : ValueField) (x z wanted : Nat) : Prop :=
  ∃ vF vG : Nat, FieldValue f F x vF ∧ FieldValue f G z vG ∧ numericalComparison vF vG = wanted

def BasePacketExact : Prop :=
  ∀ (F G : ValueField) (lowRank highRank wanted : Nat), lowRank < highRank →
    let base := basePacket F G lowRank wanted
    compile (longFieldCode F,longFieldCode G,lowRank,highRank,wanted) =
        preparedPacketCode base.1 base.2 ∧
      PreparedInput base.1 base.2

def ActualGuardedPacket : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (F G : ValueField), ProperField F → ProperField G →
  ∀ (ρ : Nat → Nat) (lowRank highRank wanted : Nat), lowRank < highRank →
    highFieldComparisonBoundCode B (longFieldCode F) (longFieldCode G) ≤ ρ lowRank →
    let packet := guardedPacket F G lowRank wanted
    PreparedInput packet.1 packet.2 ∧
    (∃ ν : Nat → Nat, PreparedTableTied f highRank ρ packet.1 ν ∧
      ∀ (j : Nat) (used : j < packet.1.length),
        lowerOperandRead f ρ (packet.1.get ⟨j,used⟩) = some (some (ν (j+1)))) ∧
    (∀ ν : Nat → Nat, PreparedTableTied f highRank ρ packet.1 ν →
      (packet.2.eval ν ↔ ρ lowRank < ν 0 ∧ actualOutcome f F G (ρ lowRank) (ν 0) wanted))

def FullStableSortedHighField : Prop := BasePacketExact ∧ ActualGuardedPacket

end LogicLineages.PermittedControl.StableSortedHighField
