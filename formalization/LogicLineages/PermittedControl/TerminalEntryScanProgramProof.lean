module
public import LogicLineages.PermittedControl.TerminalEntryScanTargets
import LogicLineages.PermittedControl.TerminalEntryScanGuardProof
import LogicLineages.PermittedControl.TerminalEntryScanNumericProof
import LogicLineages.PermittedControl.EncodedEvaluatorProof
import LogicLineages.OrdinalComparison.RawNotationCode
import Mathlib.Computability.RE

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

private theorem terminalSearch_partrec (f : Nat → Nat) (hf : Computable f) :
    Partrec (terminalSearchWith f) := by
  have h := encodedFiniteAlgorithmsPrimitiveRecursive.1.to_comp.comp (encodedStates_computable f hf)
  exact Partrec.rfind h.partrec.to₂

private theorem scan_partrec (f : Nat → Nat) (hf : Computable f) :
    Partrec (terminalEntryScanProgram f) := by
  have hs : Partrec (fun p : Nat × Nat => terminalSearchWith f p.1) :=
    (terminalSearch_partrec f hf).comp Computable.fst
  have hmap := hs.map (terminalScanAt_computable f hf)
  refine (Partrec.cond terminalEntryScanGuardExact.1.to_comp hmap (Partrec.const' (Part.some none))).of_eq
    (fun p => ?_)
  cases h : terminalScanGuard p <;> simp [terminalEntryScanProgram,h]

theorem terminalEntryScanProgram_dom (f : Nat → Nat) (p : Nat × Nat) :
    (terminalEntryScanProgram f p).Dom := by
  cases h : terminalScanGuard p with
  | false => simp [terminalEntryScanProgram,h]
  | true =>
    let a : NONote := ⟨rawNoteDecode p.1,((terminalEntryScanGuardExact.2 p).mp h).1⟩
    have he : rawNoteEncode a.1 = p.1 := rawNoteEncodeDecode p.1
    have hm := Part.mem_map (terminalScanAt f p) (firstFinite_correct f a).1
    rw [he] at hm
    simpa only [terminalEntryScanProgram,h,ite_true] using hm.1

theorem terminalEntryScanEffective : Targets.TerminalEntryScanEffective := by
  intro f
  refine ⟨terminalEntryScanProgram_dom f,fun hf => ⟨boundedTerminalEntryIndex_computable f hf,
    scan_partrec f hf,?_⟩⟩
  apply (scan_partrec f hf).of_eq_tot
  intro p
  classical
  unfold terminalEntryScanWith
  rw [Part.getOrElse_of_dom _ (terminalEntryScanProgram_dom f p) none]
  exact Part.get_mem (terminalEntryScanProgram_dom f p)

end LogicLineages.PermittedControl
