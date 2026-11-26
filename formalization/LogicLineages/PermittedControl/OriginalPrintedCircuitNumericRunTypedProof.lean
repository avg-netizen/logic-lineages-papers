module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRunTargets
import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRunBankProof
import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericReadCalibrationProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRun
open OriginalPrintedCircuitSequential (Gate run Topological)
open OriginalPrintedCircuitNumericRead (encodeGate bank packResult exactNumericGateRead)

private theorem outputCalibrates (g : Gate) : rawOutput (encodeGate g) = g.output := by
  cases g with
  | base g => cases g <;> rfl
  | field g =>
      cases g with
      | iterate k s o => rfl
      | entry P s o => cases P <;> rfl
      | count P s o => cases P <;> rfl

private theorem stepCalibrates (f : Nat → Nat) (values : List Nat) (g : Gate)
    (inputs : ∀ n ∈ g.references, n < values.length) (out : g.output < values.length) :
    step f (values,encodeGate g) =
      match g.read f (bank values) with
      | .error why => .inl (packResult (.error why))
      | .ok value => .inr (values.set g.output value) := by
  have read := exactNumericGateRead.2.2 f values g inputs
  unfold step
  change (if rawOutput (encodeGate g) < values.length then
      install (values,rawOutput (encodeGate g),OriginalPrintedCircuitNumericRead.readCode f (values,encodeGate g))
      else .inl 0) = _
  rw [outputCalibrates,if_pos out,read]
  cases seen : g.read f (bank values) with
  | error why => cases why <;> rfl
  | ok n =>
      have success : ¬ (n + 4 < 4) := by omega
      simp only [install,packResult,if_neg success,Nat.add_sub_cancel]

theorem exactNumericTypedRun : ExactNumericTypedRun := by
  intro f known gates
  induction gates generalizing known with
  | nil =>
      intro _ values _
      exact ⟨rfl,rfl⟩
  | cons g gs ih =>
      intro top values fits
      have inRange : ∀ n ∈ g.references, n < values.length := fun n hn => fits.1 n (top.1 n hn)
      have out := fits.2 g List.mem_cons_self
      have stepExact := stepCalibrates f values g inRange out
      change EncodesRun values.length
        ((gs.map encodeGate).foldl (fun st p => stepCarry f (st,p)) (step f (values,encodeGate g)))
        (run f (bank values) (g :: gs))
      rw [stepExact]
      cases seen : g.read f (bank values) with
      | error why =>
          rw [foldError,run,seen] <;> rfl
      | ok n =>
          let next := values.set g.output n
          have len : next.length = values.length := exactNumericBankUpdates.1 values g.output n
          have bankExact := exactNumericBankUpdates.2 values g.output n out
          have rest : Fits next (g.output :: known) gs := by
            constructor
            · intro n hn
              rw [len]
              rcases List.mem_cons.mp hn with eq | tail
              · subst n
                exact out
              · exact fits.1 n tail
            · intro x hx
              rw [len]
              exact fits.2 x (List.mem_cons_of_mem _ hx)
          have nextRun := ih (g.output :: known) top.2.2 next rest
          rw [run,seen]
          change EncodesRun values.length (runCode f (next,gs.map encodeGate))
            (run f (Function.update (bank values) g.output n) gs)
          rw [← bankExact]
          simpa only [len] using nextRun

end LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRun
