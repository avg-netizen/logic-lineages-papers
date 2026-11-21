module
public import LogicLineages.PermittedControl.FixedEntryClosedScanTargets
import LogicLineages.PermittedControl.FixedEntryClosedScanRawProof
import LogicLineages.PermittedControl.FixedEntryProgramProof
import LogicLineages.PermittedControl.TerminalEntryScanActualProof
import LogicLineages.OrdinalComparison.RawNormalProof
import LogicLineages.OrdinalComparison.RawNotationCode

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

theorem fixedEntryClosedActual : Targets.FixedEntryClosedActual := by
  intro f lam mu t hmu
  let p : FixedEntryClosedArgs := (rawNoteEncode lam.1,rawNoteEncode mu.1,t)
  let c := canonicalInitialCode (rawNoteEncode lam.1) t
  let a : NONote := ⟨rawNoteDecode c,(canonicalInitialCodeCorrect.2 lam t).1⟩
  have hrepr : a.1.repr = countInitial lam.1.repr t := (canonicalInitialCodeCorrect.2 lam t).2
  have hc : rawNoteEncode a.1 = c := rawNoteEncodeDecode c
  have hp : fixedEntryClosedStartTarget p = (rawNoteEncode a.1,rawNoteEncode mu.1) := by
    rw [hc] <;> rfl
  have hn : rawNormalCode p.1 = 1 := (rawNormalCorrect lam.1).mpr lam.2
  have hw : fixedEntryClosedScan f p =
      terminalEntryScanWith f (rawNoteEncode a.1,rawNoteEncode mu.1) :=
    (fixedEntryClosedRawExact.1 f p hn).trans (congrArg (terminalEntryScanWith f) hp)
  exact
    (show
      (∀ E i : Nat, fixedEntryClosedScan f p = some (some (E,i)) ↔
        FirstEntry f (countInitial lam.1.repr t) mu.1.repr i ∧
          E = entryNormAt f (countInitial lam.1.repr t) i) ∧
      (fixedEntryClosedScan f p = some none ↔
        ∀ i : Nat, ¬ FirstEntry f (countInitial lam.1.repr t) mu.1.repr i)
      from by
        rw [hw]
        simpa only [hrepr] using terminalEntryScanActual.2.1 f a mu hmu)

theorem fixedEntryClosedOriginalGraph : Targets.FixedEntryClosedOriginalGraph := by
  intro f hf lam mu t E i hmu
  exact ((fixedEntryClosedActual f lam mu t hmu).1 E i).trans
    ((fixedEntryProgramEffectivity f hf).2 lam mu t E i hmu).symm

end LogicLineages.PermittedControl
