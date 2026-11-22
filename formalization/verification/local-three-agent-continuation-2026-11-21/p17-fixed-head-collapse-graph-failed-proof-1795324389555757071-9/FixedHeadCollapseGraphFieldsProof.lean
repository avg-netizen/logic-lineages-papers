module
public import LogicLineages.PermittedControl.FixedHeadCollapseGraphTargets
import LogicLineages.PermittedControl.FixedHeadCollapseGraphCodeProof
import LogicLineages.PermittedControl.FixedEntryClosedScanRawProof
import LogicLineages.PermittedControl.FixedEntryProgramProof
import LogicLineages.PermittedControl.TerminalEntryScanActualProof
import LogicLineages.OrdinalComparison.RawNormalProof
import LogicLineages.OrdinalComparison.RawNotationCode

@[expose] public section
namespace LogicLineages.PermittedControl.FixedHeadCollapseGraph
open OrdinalComparison FieldComparison

private theorem acceptedFields (f : Nat → Nat) (p : Input) (h : domain p) :
    fields f p = some (completeEndpoint f (rawNoteDecode p.1).repr p.2,
      completeCount f (rawNoteDecode p.1).repr p.2) := by
  let lam : NONote := ⟨rawNoteDecode p.1,h.1⟩
  let c := canonicalInitialCode p.1 p.2
  have lamCode : rawNoteEncode lam.1 = p.1 := rawNoteEncodeDecode p.1
  have initial := canonicalInitialCodeCorrect.2 lam p.2
  rw [lamCode] at initial
  let a : NONote := ⟨rawNoteDecode c,initial.1⟩
  have code : rawNoteEncode a.1 = c := rawNoteEncodeDecode c
  have repr : a.1.repr = countInitial lam.1.repr p.2 := initial.2
  have normal : rawNormalCode p.1 = 1 := (rawNormalDecodeCorrect p.1).mpr h.1
  have admissible : closedProperEntryGuard (p.1,0,p.2) = true := (guardExact.2 p).mpr h
  have scan : closedProperEntryResult f (p.1,0,p.2) =
      some (some (terminalWith f (countInitial lam.1.repr p.2))) := by
    rw [closedProperEntryResult,if_pos admissible,
      fixedEntryClosedRawExact.1 f (p.1,0,p.2) normal]
    change terminalEntryScanWith f (c,0) = _
    rw [← code,← repr]
    exact terminalEntryScanActual.2.2 f a
  simp [fields,scan,Option.join,completeEndpoint,completeCount]

theorem terminalFields : ExactTerminalFields := by
  intro f p
  refine ⟨?_,acceptedFields f p⟩
  constructor
  · intro none h
    exact Option.noConfusion ((acceptedFields f p h).symm.trans none)
  · intro bad
    have rejected : guard p = false := by
      cases h : guard p with
      | false => rfl
      | true => exact (bad ((guardExact.2 p).mp h)).elim
    change closedProperEntryGuard (p.1,0,p.2) = false at rejected
    simp [fields,closedProperEntryResult,rejected]

end LogicLineages.PermittedControl.FixedHeadCollapseGraph
