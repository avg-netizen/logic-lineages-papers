module
public import LogicLineages.PermittedControl.FixedEntryClosedScanTargets
import LogicLineages.PermittedControl.FixedEntryProgramProof
import LogicLineages.PermittedControl.TerminalEntryScanProgramProof
import LogicLineages.OrdinalComparison.RawNormalProof
import Mathlib.Computability.RE

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

theorem fixedEntryClosedStartTarget_primrec : Primrec fixedEntryClosedStartTarget := by
  have hlam : Primrec (fun p : FixedEntryClosedArgs => p.1) := Primrec.fst
  have hmu : Primrec (fun p : FixedEntryClosedArgs => p.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun p : FixedEntryClosedArgs => p.2.2) := Primrec.snd.comp Primrec.snd
  exact (canonicalInitialCodeCorrect.1.comp hlam ht).pair hmu

theorem fixedEntryClosedProgram_dom (f : Nat → Nat) (p : FixedEntryClosedArgs) :
    (fixedEntryClosedProgram f p).Dom := by
  by_cases hn : rawNormalCode p.1 = 1
  · rw [fixedEntryClosedProgram, if_pos hn]
    exact terminalEntryScanProgram_dom f (fixedEntryClosedStartTarget p)
  · simp [fixedEntryClosedProgram,hn]

private theorem fixedEntryClosedProgram_partrec (f : Nat → Nat) (hf : Computable f) :
    Partrec (fixedEntryClosedProgram f) := by
  have hnorm : Primrec rawNormalCode := Primrec.nat_iff.mpr rawNormalPrimitiveRecursive
  have hlam : Primrec (fun p : FixedEntryClosedArgs => p.1) := Primrec.fst
  have hguard : PrimrecPred (fun p : FixedEntryClosedArgs => rawNormalCode p.1 = 1) :=
    Primrec.eq.comp (hnorm.comp hlam) (Primrec.const 1)
  have hbranch := ((terminalEntryScanEffective f).2 hf).2.1.comp
    fixedEntryClosedStartTarget_primrec.to_comp
  exact (Partrec.cond hguard.decide.to_comp hbranch (Partrec.const' (Part.some none))).of_eq
    (fun p => by by_cases h : rawNormalCode p.1 = 1 <;> simp [fixedEntryClosedProgram,h])

theorem fixedEntryClosedEffective : Targets.FixedEntryClosedEffective := by
  refine ⟨fixedEntryClosedStartTarget_primrec,?_⟩
  intro f
  refine ⟨fixedEntryClosedProgram_dom f, fun hf => ⟨fixedEntryClosedProgram_partrec f hf,?_⟩⟩
  apply (fixedEntryClosedProgram_partrec f hf).of_eq_tot
  intro p
  classical
  unfold fixedEntryClosedScan
  rw [Part.getOrElse_of_dom _ (fixedEntryClosedProgram_dom f p) none]
  exact Part.get_mem (fixedEntryClosedProgram_dom f p)

end LogicLineages.PermittedControl
