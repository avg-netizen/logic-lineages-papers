module
public import LogicLineages.PermittedControl.HighFieldPreparedActualTargets
import LogicLineages.PermittedControl.HighFieldPreparedPacketShapeProof
import LogicLineages.PermittedControl.InverseComparisonPreparedRowsSemanticProof
import LogicLineages.PermittedControl.ClosedOrdinaryFieldActualProof
import LogicLineages.PermittedControl.FieldComparisonProof

@[expose] public section
namespace LogicLineages.PermittedControl.HighFieldPreparedPacket
open OrdinalComparison FieldComparison
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection

def Witness (f ρ : Nat → Nat) (rankF rankG : Nat) (packet : PreparedPacketCode) (test : Prop) : Prop :=
  ∃ (table : List LowerOperand) (p : NormalForm.Formula),
    packet = preparedPacketCode table p ∧ PreparedInput table p ∧ table.length ≤ 1 ∧
    (∀ op ∈ table, ∃ H : ValueField, op = .ordinary (min rankF rankG) H) ∧
    (∃ ν : Nat → Nat,
      ν 0 = ρ (max rankF rankG) ∧ PreparedTableTied f (max rankF rankG) ρ table ν ∧
      ∀ (j : Nat) (used : j < table.length),
        lowerOperandRead f ρ (table.get ⟨j,used⟩) = some (some (ν (j+1)))) ∧
    (∀ ν : Nat → Nat, ν 0 = ρ (max rankF rankG) →
      PreparedTableTied f (max rankF rankG) ρ table ν → (p.eval ν ↔ test))

private theorem emptyWitness (f ρ : Nat → Nat) (rankF rankG : Nat) {packet : PreparedPacketCode}
    {p : NormalForm.Formula} {test : Prop} (code : packet = preparedPacketCode [] p)
    (shape : PreparedInput [] p) (meaning : ∀ ν : Nat → Nat, p.eval ν ↔ test) :
    Witness f ρ rankF rankG packet test := by
  refine ⟨[],p,code,shape,by simp,?_,?_,?_⟩
  · intro op mem
    simp at mem
  · refine ⟨fun _ => ρ (max rankF rankG),rfl,?_,?_⟩
    · intro j used
      simp at used
    · intro j used
      simp at used
  · intro ν _ _
    exact meaning ν

theorem invalidWitness (f ρ : Nat → Nat) (form : OrientedHighFormCode)
    (rankF rankG wanted result : Nat) (invalid : 2 < wanted) (range : result ≤ 2) :
    Witness f ρ rankF rankG (postprocess (form,rankF,rankG,wanted)) (result = wanted) := by
  apply emptyWitness f ρ rankF rankG (packetExact.1 form rankF rankG wanted invalid) packetShape.1
  intro ν
  change False ↔ result = wanted
  exact ⟨False.elim,fun h => (not_le_of_gt invalid) (h ▸ range)⟩

theorem constantWitness (f ρ : Nat → Nat) (orientation answer rankF rankG wanted result : Nat)
    (admitted : wanted ≤ 2) (same : flipHighComparisonAnswer orientation answer = result) :
    Witness f ρ rankF rankG (postprocess ((orientation,rawConstForm answer),rankF,rankG,wanted))
      (result = wanted) := by
  apply emptyWitness f ρ rankF rankG (packetExact.2.1 orientation answer rankF rankG wanted admitted)
    (packetShape.2.1 orientation answer wanted)
  intro ν
  by_cases agrees : result = wanted <;>
    simp [constantFormula,same,agrees,NormalForm.Formula.eval]

theorem linearWitness (f ρ : Nat → Nat) (orientation sign rankF rankG wanted : Nat)
    (H : ValueField) (h valueP valueQ : Nat) {test : Prop}
    (admitted : wanted ≤ 2) (range : sign ≤ 2)
    (lowest : lowerRank orientation rankF rankG = min rankF rankG)
    (strict : lowerRank orientation rankF rankG < max rankF rankG)
    (positive : 0 < ρ (max rankF rankG))
    (domain : ClosedOrdinaryValueDomain H (ρ (lowerRank orientation rankF rankG)))
    (actual : FieldValue f H (ρ (lowerRank orientation rankF rankG)) h)
    (printed : InverseTableRows sign (ρ (max rankF rankG)) h valueQ valueP)
    (comparison : (numericalComparison valueP valueQ = sortedWanted orientation wanted) ↔ test) :
    Witness f ρ rankF rankG
      (postprocess ((orientation,rawLinearForm sign (longFieldCode H)),rankF,rankG,wanted)) test := by
  let op : LowerOperand := .ordinary (lowerRank orientation rankF rankG) H
  let ν : Nat → Nat := fun name => if name = 0 then ρ (max rankF rankG) else h
  have lowerActual : LowerOperandActual f ρ op h := ⟨domain,actual⟩
  have read : lowerOperandRead f ρ op = some (some h) :=
    (((closedOrdinaryValueActual f H (ρ (lowerRank orientation rankF rankG))).2 domain).1 h).mpr actual
  have exactCode := packetExact.2.2 orientation sign rankF rankG wanted H admitted
  have shape := packetShape.2.2 orientation sign rankF rankG wanted H
  refine ⟨[op],InverseComparisonPreparedRows.emitFormula sign (sortedWanted orientation wanted),
    exactCode,shape,by simp,?_,?_,?_⟩
  · intro item used
    have same : item = op := List.mem_singleton.mp used
    subst item
    exact ⟨H,by simp [op,lowest]⟩
  · refine ⟨ν,by simp [ν],?_,?_⟩
    · intro j used
      have length : j < 1 := used
      have index : j = 0 := by omega
      subst j
      exact ⟨strict,by simpa [ν] using lowerActual⟩
    · intro j used
      have length : j < 1 := used
      have index : j = 0 := by omega
      subst j
      simpa [ν] using read
  · intro assignment highest tied
    have lower := tied 0 (by simp)
    have field : FieldValue f H (ρ (lowerRank orientation rankF rankG)) (assignment 1) := lower.2.2
    have same := fieldValueUnique f H _ (assignment 1) h field actual
    have transferred : InverseTableRows sign (assignment 0) (assignment 1) valueQ valueP := by
      rw [highest,same]
      exact printed
    have positiveAssignment : 0 < assignment 0 := by simpa only [highest] using positive
    exact (InverseComparisonPreparedRows.actualInverseRows sign (sortedWanted orientation wanted)
      valueP valueQ assignment range positiveAssignment transferred).trans comparison

end LogicLineages.PermittedControl.HighFieldPreparedPacket
