module
public import LogicLineages.PermittedControl.ClosedOrdinaryFieldTargets
import LogicLineages.PermittedControl.ClosedOrdinaryFieldGuardProof
import LogicLineages.PermittedControl.FixedEntryClosedScanRawProof
import LogicLineages.PermittedControl.FixedEntryClosedScanActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.FieldComparison
open OrdinalComparison

theorem closedProperEntryResultExact : ClosedProperEntryResultExact := by
  refine ⟨?_,?_⟩
  · intro f p
    cases h : closedProperEntryGuard p with
    | false =>
      have hn : ¬DecodedClosedProperEntryDomain p := by
        intro hd
        have he := (closedProperEntryDomainExact.2.1 p).mpr hd
        rw [h] at he
        contradiction
      simp [closedProperEntryResult,h,hn]
    | true =>
      have hd := (closedProperEntryDomainExact.2.1 p).mp h
      have hn : fixedEntryClosedScan f p ≠ none :=
        fun he => (fixedEntryClosedRawExact.2 f p).mp he ⟨hd.1,hd.2.1,hd.2.2.2.1⟩
      simp [closedProperEntryResult,h,hn,hd]
  · intro f lam mu x hd
    have h := (closedProperEntryDomainExact.2.2 lam mu x).mpr hd
    simpa only [closedProperEntryResult,h,if_true] using fixedEntryClosedActual f lam mu x hd.1.2.1

theorem proper_entry_none_iff (f : Nat → Nat) (lam mu : NONote) (x : Nat) :
    closedProperEntryResult f (rawNoteEncode lam.1,rawNoteEncode mu.1,x) = none ↔
      ¬ClosedOrdinaryValueDomain (.entry 0 lam mu) x := by
  let p : FixedEntryClosedArgs :=
    (rawNoteEncode lam.1,rawNoteEncode mu.1,x)
  have hd := (closedProperEntryDomainExact.2.1 p).symm.trans (closedProperEntryDomainExact.2.2 lam mu x)
  exact (closedProperEntryResultExact.1 f p).trans (not_congr hd)

end LogicLineages.PermittedControl.FieldComparison
