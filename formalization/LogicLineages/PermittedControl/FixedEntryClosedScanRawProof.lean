module
public import LogicLineages.PermittedControl.FixedEntryClosedScanTargets
import LogicLineages.PermittedControl.FixedEntryProgramProof
import LogicLineages.PermittedControl.TerminalEntryScanGuardProof
import LogicLineages.PermittedControl.TerminalEntryScanProgramProof
import LogicLineages.PermittedControl.TerminalEntryScanActualProof
import LogicLineages.OrdinalComparison.RawNormalProof
import LogicLineages.OrdinalComparison.RawNotationCode

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

private theorem fixed_realization_of_mem {f : Nat → Nat} {p : FixedEntryClosedArgs}
    {r : TerminalEntryScanResult} (hr : r ∈ fixedEntryClosedProgram f p) :
    fixedEntryClosedScan f p = r := by
  classical
  unfold fixedEntryClosedScan
  exact (Part.getOrElse_of_dom _ hr.1 none).trans (Part.get_eq_of_mem hr hr.1)

private theorem fixed_normal_lam (f : Nat → Nat) (p : FixedEntryClosedArgs)
    (hl : rawNormalCode p.1 = 1) :
    fixedEntryClosedScan f p = terminalEntryScanWith f (fixedEntryClosedStartTarget p) := by
  let q := fixedEntryClosedStartTarget p
  have hdom := terminalEntryScanProgram_dom f q
  have hm : terminalEntryScanWith f q ∈ terminalEntryScanProgram f q := by
    classical
    unfold terminalEntryScanWith
    rw [Part.getOrElse_of_dom _ hdom none]
    exact Part.get_mem hdom
  apply fixed_realization_of_mem
  simpa only [fixedEntryClosedProgram,if_pos hl] using hm

theorem fixedEntryClosedRawExact : Targets.FixedEntryClosedRawExact := by
  refine ⟨fixed_normal_lam,?_⟩
  intro f p
  by_cases hl : rawNormalCode p.1 = 1
  · have hln := (rawNormalDecodeCorrect p.1).mp hl
    let lam : NONote := ⟨rawNoteDecode p.1,hln⟩
    have hcode : rawNoteEncode lam.1 = p.1 := rawNoteEncodeDecode p.1
    have hA : ONote.NF (rawNoteDecode (fixedEntryClosedStartTarget p).1) := by
      change ONote.NF (rawNoteDecode (canonicalInitialCode p.1 p.2.2))
      rw [← hcode]
      exact (canonicalInitialCodeCorrect.2 lam p.2.2).1
    rw [fixed_normal_lam f p hl,terminalEntryScanActual.1 f (fixedEntryClosedStartTarget p)]
    have hguard := terminalEntryScanGuardExact.2 (fixedEntryClosedStartTarget p)
    constructor
    · intro hf hvalid
      have ht := hguard.mpr ⟨hA,hvalid.2.1,hvalid.2.2⟩
      rw [ht] at hf
      contradiction
    · intro hn
      cases h : terminalScanGuard (fixedEntryClosedStartTarget p) with
      | false => rfl
      | true =>
        have ht := hguard.mp h
        exact (hn ⟨hln,ht.2.1,ht.2.2⟩).elim
  · have hnone : fixedEntryClosedScan f p = none := by
      apply fixed_realization_of_mem
      simp [fixedEntryClosedProgram,hl]
    constructor
    · rintro _ ⟨hn,_,_⟩
      exact hl ((rawNormalDecodeCorrect p.1).mpr hn)
    · intro _
      exact hnone

end LogicLineages.PermittedControl
