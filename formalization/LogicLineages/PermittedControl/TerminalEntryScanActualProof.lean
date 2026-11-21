module
public import LogicLineages.PermittedControl.TerminalEntryScanTargets
import LogicLineages.PermittedControl.TerminalEntryScanGuardProof
import LogicLineages.PermittedControl.TerminalEntryScanPrefixProof
import LogicLineages.PermittedControl.EntryEffectivityProof
import LogicLineages.PermittedControl.TerminalProof
import LogicLineages.OrdinalComparison.ActualFiniteHead
import LogicLineages.OrdinalComparison.RawNormCode
import LogicLineages.OrdinalComparison.RawNotationCode

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

private theorem scan_realization {f : Nat → Nat} {p : Nat × Nat} {r : TerminalEntryScanResult}
    (hm : r ∈ terminalEntryScanProgram f p) : terminalEntryScanWith f p = r := by
  classical
  unfold terminalEntryScanWith
  exact (Part.getOrElse_of_dom _ hm.1 none).trans (Part.get_eq_of_mem hm hm.1)

private theorem scan_at_terminal {f : Nat → Nat} {p : Nat × Nat} {T : Nat}
    (hg : terminalScanGuard p = true) (hT : T ∈ terminalSearchWith f p.1) :
    terminalEntryScanWith f p = terminalScanAt f p T := by
  apply scan_realization
  simpa only [terminalEntryScanProgram,hg,ite_true] using Part.mem_map (terminalScanAt f p) hT

private theorem no_hit_eq (f : Nat → Nat) (p : Nat × Nat) (T : Nat) :
    terminalScanAt f p T = some none ↔ boundedTerminalEntryIndex f p.1 p.2 T = 0 := by
  cases h : boundedTerminalEntryIndex f p.1 p.2 T <;> simp [terminalScanAt,h]

private theorem hit_eq (f : Nat → Nat) (p : Nat × Nat) (T E i : Nat) :
    terminalScanAt f p T = some (some (E,i)) ↔
      boundedTerminalEntryIndex f p.1 p.2 T = i+1 ∧ E = rawNormCode (encodedStatesWith f p.1 i) := by
  cases h : boundedTerminalEntryIndex f p.1 p.2 T with
  | zero => simp [terminalScanAt,h]
  | succ j =>
    by_cases hj : j = i
    · subst j
      simp [terminalScanAt,h,eq_comm]
    · simp [terminalScanAt,h,hj]

private theorem scan_invalid_iff (f : Nat → Nat) (p : Nat × Nat) :
    terminalEntryScanWith f p = none ↔ terminalScanGuard p = false := by
  cases hg : terminalScanGuard p with
  | false =>
    have h : terminalEntryScanWith f p = none := by
      apply scan_realization
      simp [terminalEntryScanProgram,hg]
    simp [h]
  | true =>
    let a : NONote := ⟨rawNoteDecode p.1,((terminalEntryScanGuardExact.2 p).mp hg).1⟩
    have hc : rawNoteEncode a.1 = p.1 := rawNoteEncodeDecode p.1
    have hT := (firstFinite_correct f a).1
    rw [hc] at hT
    rw [scan_at_terminal hg hT]
    cases h : boundedTerminalEntryIndex f p.1 p.2 (terminalWith f a.1.repr).2 <;> simp [terminalScanAt,h]

private theorem guard_normal_entry (a mu : NONote)
    (hmu : mu.1.repr = 0 ∨ Order.IsSuccLimit mu.1.repr) :
    terminalScanGuard (rawNoteEncode a.1,rawNoteEncode mu.1) = true := by
  apply (terminalEntryScanGuardExact.2 _).mpr
  have ha : rawNoteDecode (rawNoteEncode a.1) = a.1 := rawNoteDecodeEncode a.1
  have hm : rawNoteDecode (rawNoteEncode mu.1) = mu.1 := rawNoteDecodeEncode mu.1
  change ONote.NF (rawNoteDecode (rawNoteEncode a.1)) ∧
    ONote.NF (rawNoteDecode (rawNoteEncode mu.1)) ∧
    ((rawNoteDecode (rawNoteEncode mu.1)).repr = 0 ∨
      Order.IsSuccLimit (rawNoteDecode (rawNoteEncode mu.1)).repr)
  rw [ha,hm]
  exact ⟨a.2,mu.2,hmu⟩

private theorem retained_index_iff (f : Nat → Nat) (a mu : NONote)
    (hmu : mu.1.repr = 0 ∨ Order.IsSuccLimit mu.1.repr) (i : Nat) :
    boundedTerminalEntryIndex f (rawNoteEncode a.1) (rawNoteEncode mu.1)
      (terminalWith f a.1.repr).2 = i + 1 ↔ FirstEntry f a.1.repr mu.1.repr i := by
  rw [(boundedTerminalEntryIndexExact f (rawNoteEncode a.1) (rawNoteEncode mu.1)
    (terminalWith f a.1.repr).2).2 i]
  constructor
  · rintro ⟨_,htrue,hbef⟩
    have hi := (entry_test_iff f a mu hmu i).mp (of_decide_eq_true htrue)
    refine ⟨hi.1,hi.2,fun j hj hinterval => ?_⟩
    exact (of_decide_eq_false (hbef j hj)) ((entry_test_iff f a mu hmu j).mpr hinterval)
  · intro hi
    refine ⟨firstEntry_le_terminal f a.1.repr mu.1.repr (normalRepresentationSound a) hmu i hi,?_,?_⟩
    · exact decide_eq_true ((entry_test_iff f a mu hmu i).mpr ⟨hi.1,hi.2.1⟩)
    · intro j hj
      apply decide_eq_false
      intro ht
      exact hi.2.2 j hj ((entry_test_iff f a mu hmu j).mp ht)

private theorem retained_norm (f : Nat → Nat) (a : NONote) (i : Nat)
    (hi : i ≤ (terminalWith f a.1.repr).2) :
    rawNormCode (encodedStatesWith f (rawNoteEncode a.1) i) = entryNormAt f a.1.repr i := by
  have ht := trajectory_correct f a i hi
  let r : NONote := ⟨rawNoteDecode (encodedStatesWith f (rawNoteEncode a.1) i),ht.1⟩
  have h := rawNormCodeCorrect r.1
  rw [rawNoteEncodeDecode, ← actualOrdinalNorm_notationCorrespondence r] at h
  simpa only [entryNormAt,r,ht.2] using h

private theorem scan_actual_graph (f : Nat → Nat) (a mu : NONote)
    (hmu : mu.1.repr = 0 ∨ Order.IsSuccLimit mu.1.repr) :
    let p := (rawNoteEncode a.1,rawNoteEncode mu.1)
    (∀ E i : Nat, terminalEntryScanWith f p = some (some (E,i)) ↔
      FirstEntry f a.1.repr mu.1.repr i ∧ E = entryNormAt f a.1.repr i) ∧
    (terminalEntryScanWith f p = some none ↔ ∀ i : Nat, ¬ FirstEntry f a.1.repr mu.1.repr i) := by
  have hout := scan_at_terminal (guard_normal_entry a mu hmu) (firstFinite_correct f a).1
  refine ⟨?_,?_⟩
  · intro E i
    rw [hout,hit_eq,retained_index_iff f a mu hmu i]
    constructor
    · rintro ⟨hi,hE⟩
      have hb := firstEntry_le_terminal f a.1.repr mu.1.repr (normalRepresentationSound a) hmu i hi
      exact ⟨hi,hE.trans (retained_norm f a i hb)⟩
    · rintro ⟨hi,hE⟩
      have hb := firstEntry_le_terminal f a.1.repr mu.1.repr (normalRepresentationSound a) hmu i hi
      exact ⟨hi,hE.trans (retained_norm f a i hb).symm⟩
  · rw [hout,no_hit_eq]
    constructor
    · intro hz i hi
      have hn := (retained_index_iff f a mu hmu i).mpr hi
      rw [hz] at hn
      omega
    · intro hno
      cases h : boundedTerminalEntryIndex f (rawNoteEncode a.1) (rawNoteEncode mu.1)
        (terminalWith f a.1.repr).2 with
      | zero => rfl
      | succ i => exact (hno i ((retained_index_iff f a mu hmu i).mp h)).elim

private theorem scan_zero_target (f : Nat → Nat) (a : NONote) :
    terminalEntryScanWith f (rawNoteEncode a.1,0) = some (some (terminalWith f a.1.repr)) := by
  let T := (terminalWith f a.1.repr).2
  let E := (terminalWith f a.1.repr).1
  have hfin := terminal_firstFinite f a.1.repr (normalRepresentationSound a)
  have hentry : FirstEntry f a.1.repr 0 T := by
    refine ⟨zero_le,?_,?_⟩
    · simpa only [T,hfin.1,zero_add] using Ordinal.natCast_lt_omega0 E
    · intro j hj hinterval
      exact (not_lt_of_ge (hfin.2 j hj)) (by simpa only [zero_add] using hinterval.2)
  have hnorm : E = entryNormAt f a.1.repr T := by
    unfold entryNormAt
    change E = actualOrdinalNorm ((descentWith f)^[((terminalWith f a.1.repr).2)] a.1.repr)
    rw [hfin.1]
    symm
    simpa only [Nat.cast_zero,mul_zero,zero_add,Nat.zero_mul] using actualFiniteHeadNorm 0 E
  have hzero : rawNoteEncode (NONote.ofNat 0).1 = 0 := by
    simp only [NONote.ofNat, ONote.ofNat, rawNoteEncode]
  have hh := ((scan_actual_graph f a (NONote.ofNat 0) (Or.inl rfl)).1 E T).mpr ⟨hentry,hnorm⟩
  simpa only [hzero,E,T,Prod.eta] using hh

theorem terminalEntryScanActual : Targets.TerminalEntryScanActual :=
  ⟨scan_invalid_iff,scan_actual_graph,scan_zero_target⟩

end LogicLineages.PermittedControl
