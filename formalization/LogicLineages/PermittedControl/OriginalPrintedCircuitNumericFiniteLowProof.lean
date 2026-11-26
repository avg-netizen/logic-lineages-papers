module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericFiniteLowTargets
import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericFiniteLowUnifiedProof
import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericFiniteLowLayoutProof
import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRunBankProof
import LogicLineages.PermittedControl.OriginalPrintedCircuitNormalizedTerminalProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNumericFiniteLow
open OriginalPrintedCircuitNumericRead (bank encodeGate packResult)
open OriginalPrintedCircuitNumericRun (Fits exactNumericBankUpdates)
open OriginalPrintedCircuitNumericPlainTerminal (packTerminal boolCode)
open OriginalPrintedCircuitSequential (Failure)
open OriginalPrintedCircuitTerminal (observe)
open OriginalPrintedCircuitNormalizedTerminal (exactPrintedNormalizedTerminal)

private theorem packedBoolean (r : Except Failure Bool) (b : Bool) :
    packTerminal r = boolCode b ↔ r = .ok b := by
  cases r with
  | error why => cases why <;> cases b <;> simp [packTerminal,packResult,boolCode]
  | ok x => cases x <;> cases b <;> simp [packTerminal,boolCode]

theorem exactNumericPrintedFiniteLow : ExactNumericPrintedFiniteLow := by
  intro f known gates top values rank bound p fits isExternal hp refs
  let args := typedArgs values gates rank bound p
  have inRange := fits.1 rank isExternal
  have actualPoint (a : Nat) : lowPoint f args a =
      packTerminal (observe f (Function.update (bank values) rank a) gates p) := by
    let vals := values.set rank a
    have sameLength : vals.length = values.length := exactNumericBankUpdates.1 values rank a
    have fit : Fits vals known gates := by
      refine ⟨?_,?_⟩
      · intro n hn
        rw [sameLength]
        exact fits.1 n hn
      · intro g hg
        rw [sameLength]
        exact fits.2 g hg
    have all : ∀ n ∈ p.names, n < vals.length := by
      rw [sameLength]
      exact refs
    have cal := exactUnifiedNumericTerminal.2.2 f known gates top vals p fit hp all
    change (if rank < values.length then observeCode f (vals,gates.map encodeGate,encodeTest p)
      else 0) = _
    rw [if_pos inRange,cal]
    rw [exactNumericBankUpdates.2 values rank a inRange]
  have layout := (exactNumericFiniteLowLayout.2 f args).2
  have point (a : Nat) (b : Bool) :
      (a,boolCode b) ∈ lowTable f args ↔
        a < bound ∧ LiftedAt f known gates (Function.update (bank values) rank a) p b := by
    rw [layout a (boolCode b),actualPoint a]
    have term := exactPrintedNormalizedTerminal f known gates top (Function.update (bank values) rank a) p hp b
    constructor
    · rintro ⟨within,h⟩
      exact ⟨within,term.mp ((packedBoolean _ b).mp h.symm)⟩
    · rintro ⟨within,h⟩
      exact ⟨within,((packedBoolean _ b).mpr (term.mpr h)).symm⟩
  refine ⟨actualPoint,point,?_⟩
  intro b
  change (lowTable f args).any (fun r => decide (r.2 = boolCode b)) = true ↔ _
  rw [List.any_eq_true]
  constructor
  · rintro ⟨⟨a,code⟩,member,accepted⟩
    have same : code = boolCode b := of_decide_eq_true accepted
    subst code
    exact ⟨a,(point a b).mp member⟩
  · rintro ⟨a,within,actual⟩
    exact ⟨(a,boolCode b),(point a b).mpr ⟨within,actual⟩,decide_eq_true rfl⟩

end LogicLineages.PermittedControl.OriginalPrintedCircuitNumericFiniteLow
