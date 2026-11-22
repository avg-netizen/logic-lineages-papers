module
public import LogicLineages.PermittedControl.OriginalMatrixActualHighPacketTargets
import LogicLineages.PermittedControl.OriginalMatrixPaidOrderRowProof
import LogicLineages.PermittedControl.OriginalMatrixPaidCongruenceMatrixProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixActualHighPacket
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)
open OriginalMatrixPaidOrderRow (exactPaidSourceOrderRow)
open OriginalMatrixPaidCongruence (exactPaidCongruenceMatrix)
open OriginalMatrixUniformHighBound (Funds)

private theorem alignedTraces (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (strict : StrictMono ρ) (r z : Nat) (rs : List Row)
    (ranked : ∀ row ∈ rs, ∀ t ∈ row.2.2, t.2.rank < r ∧ t.2.rank ≤ z)
    (paid : ∀ row ∈ rs, Funds B r z ρ row) (values : Snapshot)
    (actual : actualRows f ρ rs values) :
    OrderedTraces f B ρ r z rs values := by
  induction rs generalizing values with
  | nil =>
      cases values with
      | nil => exact True.intro
      | cons value values => exact False.elim actual
  | cons row rows ih =>
      cases values with
      | nil => exact False.elim actual
      | cons value values =>
          rcases value with ⟨v,b⟩
          refine ⟨?_,ih (fun q hq => ranked q (List.mem_cons_of_mem _ hq))
            (fun q hq => paid q (List.mem_cons_of_mem _ hq)) values actual.2.2.2⟩
          intro order
          have head : actualRows f ρ [row] [(v,b)] :=
            ⟨actual.1,actual.2.1,actual.2.2.1,True.intro⟩
          have funds := (paid row List.mem_cons_self).2 order
          exact exactPaidSourceOrderRow f B hf ρ strict r z row v b order head
            (ranked row List.mem_cons_self) funds.1 funds.2

theorem exactActualHighPacket : ExactActualHighPacket := by
  intro f B hf ρ strict r z rs ranked paid values
  have modular := exactPaidCongruenceMatrix f B hf ρ rs (fun row mem => (paid row mem).1) values
  constructor
  · intro actual
    exact ⟨modular.mp actual,alignedTraces f B hf ρ strict r z rs ranked paid values actual⟩
  · intro packet
    exact modular.mpr packet.1

end LogicLineages.PermittedControl.OriginalMatrixActualHighPacket
