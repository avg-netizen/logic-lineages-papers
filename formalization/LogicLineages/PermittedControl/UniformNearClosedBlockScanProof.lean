module
public import LogicLineages.PermittedControl.ClosedOrdinaryFieldTargets
import LogicLineages.PermittedControl.UniformNearClosedBlockEntryProof
import LogicLineages.PermittedControl.EncodedEvaluatorProof
import LogicLineages.PermittedControl.TerminalEntryScanGuardProof
import LogicLineages.PermittedControl.TerminalEntryScanProgramProof
import LogicLineages.PermittedControl.FixedEntryClosedScanEffectiveProof
import LogicLineages.PermittedControl.ClosedOrdinaryFieldGuardProof
import LogicLineages.OrdinalComparison.RawNormCode
import LogicLineages.OrdinalComparison.RawSplitProof
import LogicLineages.OrdinalComparison.RawNormalProof
import Mathlib.Computability.RE

/-! Parametric copies of the per-control effectivity proofs of the entry
scan and the closed ordinary fields: the control is `F a` for a context
`a : α`, and computability is joint in `a`. Same constructions, same order,
with `hF.comp` in place of `hf.comp`. -/

public section
namespace LogicLineages.PermittedControl.UniformNearClosedBlock
open OrdinalComparison
open FieldComparison (closedProperEntryResult closedOrdinaryValueField closedOrdinaryCountField
  closedProperEntryGuard closedProperEntryDomainExact LongFieldCode)

attribute [local irreducible] rawSplitCode rawNormCode rawNormalCode encodedMaximumPredecessor
  encodedFiniteTest encodedFiniteValue Nat.unpair Nat.sqrt

variable {α : Type} [Primcodable α]

theorem searchParam (F : α → Nat → Nat) (hF : Computable₂ F) :
    Partrec (fun x : α × Nat => terminalSearchWith (F x.1) x.2) := by
  have hstate : Computable (fun y : (α × Nat) × Nat => encodedStatesWith (F y.1.1) y.1.2 y.2) :=
    (statesParam F hF).comp ((Computable.fst.comp Computable.fst).pair
      ((Computable.snd.comp Computable.fst).pair Computable.snd))
  have h := encodedFiniteAlgorithmsPrimitiveRecursive.1.to_comp.comp hstate
  exact Partrec.rfind h.partrec.to₂

theorem scanProgramParam (F : α → Nat → Nat) (hF : Computable₂ F) :
    Partrec (fun x : α × (Nat × Nat) => terminalEntryScanProgram (F x.1) x.2) := by
  have hs : Partrec (fun x : α × (Nat × Nat) => terminalSearchWith (F x.1) x.2.1) :=
    (searchParam F hF).comp (Computable.fst.pair (Computable.fst.comp Computable.snd))
  have hat : Computable₂ (fun (x : α × (Nat × Nat)) (T : Nat) => terminalScanAt (F x.1) x.2 T) :=
    (scanAtParam F hF).comp ((Computable.fst.comp Computable.fst).pair
      ((Computable.snd.comp Computable.fst).pair Computable.snd))
  have hmap := hs.map hat
  have hguard : Computable (fun x : α × (Nat × Nat) => terminalScanGuard x.2) :=
    terminalEntryScanGuardExact.1.to_comp.comp Computable.snd
  refine (Partrec.cond hguard hmap (Partrec.const' (Part.some none))).of_eq (fun x => ?_)
  cases h : terminalScanGuard x.2 <;> simp [terminalEntryScanProgram,h]

theorem closedProgramParam (F : α → Nat → Nat) (hF : Computable₂ F) :
    Partrec (fun x : α × FixedEntryClosedArgs => fixedEntryClosedProgram (F x.1) x.2) := by
  have hnorm : Primrec rawNormalCode := Primrec.nat_iff.mpr rawNormalPrimitiveRecursive
  have hguard : Computable (fun x : α × FixedEntryClosedArgs => decide (rawNormalCode x.2.1 = 1)) :=
    (Primrec.eq.comp (hnorm.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const 1)).decide.to_comp
  have hbranch := (scanProgramParam F hF).comp
    (Computable.fst.pair (fixedEntryClosedStartTarget_primrec.to_comp.comp Computable.snd))
  exact (Partrec.cond hguard hbranch (Partrec.const' (Part.some none))).of_eq
    (fun x => by by_cases h : rawNormalCode x.2.1 = 1 <;> simp [fixedEntryClosedProgram,h])

theorem closedScanParam (F : α → Nat → Nat) (hF : Computable₂ F) :
    Computable (fun x : α × FixedEntryClosedArgs => fixedEntryClosedScan (F x.1) x.2) := by
  apply (closedProgramParam F hF).of_eq_tot
  intro x
  classical
  unfold fixedEntryClosedScan
  rw [Part.getOrElse_of_dom _ (fixedEntryClosedProgram_dom (F x.1) x.2) none]
  exact Part.get_mem (fixedEntryClosedProgram_dom (F x.1) x.2)

end LogicLineages.PermittedControl.UniformNearClosedBlock
