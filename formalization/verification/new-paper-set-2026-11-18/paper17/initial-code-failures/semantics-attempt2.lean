module
public import LogicLineages.PermittedControl.InitialCodeShapeProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem normal_code_finite_eq (c n : Nat) (hc : ONote.NF (rawNoteDecode c)) :
    c=rawNoteEncode (ONote.ofNat n) ↔ (rawNoteDecode c).repr=(n : Ordinal) := by
  constructor
  · intro h
    rw [h,rawNoteDecodeEncode]
    simp
  · intro h
    letI : ONote.NF (rawNoteDecode c) := hc
    have he : rawNoteDecode c=ONote.ofNat n := ONote.repr_inj.mp (by simpa using h)
    have hh := congrArg rawNoteEncode he
    rwa [rawNoteEncodeDecode] at hh

 theorem normal_code_lt_two (c : Nat) (hc : ONote.NF (rawNoteDecode c)) :
    rawComparisonCode c (rawNoteEncode (ONote.ofNat 2))=0 ↔ (rawNoteDecode c).repr<2 := by
  have h := (rawComparisonOrdinalCorrect (⟨rawNoteDecode c,hc⟩ : NONote) (NONote.ofNat 2)).1
  change rawComparisonCode (rawNoteEncode (rawNoteDecode c)) (rawNoteEncode (ONote.ofNat 2))=0 ↔
    (rawNoteDecode c).repr<(ONote.ofNat 2).repr at h
  simpa only [rawNoteEncodeDecode,ONote.repr_ofNat] using h

 theorem normal_code_ge_three (c : Nat) (hc : ONote.NF (rawNoteDecode c)) :
    rawComparisonCode (rawNoteEncode (ONote.ofNat 3)) c ≠ 2 ↔ (3 : Ordinal) ≤ (rawNoteDecode c).repr := by
  have h := (rawComparisonOrdinalCorrect (NONote.ofNat 3) (⟨rawNoteDecode c,hc⟩ : NONote)).2.2
  change rawComparisonCode (rawNoteEncode (ONote.ofNat 3)) (rawNoteEncode (rawNoteDecode c))=2 ↔
    (rawNoteDecode c).repr<(ONote.ofNat 3).repr at h
  simpa only [rawNoteEncodeDecode,ONote.repr_ofNat,not_lt] using not_congr h

 theorem code_list_ones (l : List Nat) (hn : ∀ c ∈ l, ONote.NF (rawNoteDecode c)) :
    l.all (fun c => decide (c=rawNoteEncode (ONote.ofNat 1)))=true ↔
      l.map (fun c => (rawNoteDecode c).repr)=List.replicate l.length (1 : Ordinal) := by
  rw [List.all_eq_true,List.eq_replicate_iff]
  constructor
  · intro h
    refine ⟨by simp,?_⟩
    intro e he
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp he
    exact (normal_code_finite_eq c 1 (hn c hc)).mp (of_decide_eq_true (h c hc))
  · rintro ⟨_,h⟩ c hc
    exact decide_eq_true ((normal_code_finite_eq c 1 (hn c hc)).mpr (h _ (List.mem_map.mpr ⟨c,hc,rfl⟩)))

 theorem quadratic_remainder_actual (l : List Nat) (hn : ∀ c ∈ l, ONote.NF (rawNoteDecode c)) :
    originalQuadraticRemainder l=true ↔ ∃ n : Nat,
      l.map (fun c => (rawNoteDecode c).repr)=(2 : Ordinal)::List.replicate n 1 := by
  cases l with
  | nil => simp [originalQuadraticRemainder]
  | cons c l =>
    have hc := hn c List.mem_cons_self
    have hl : ∀ x ∈ l, ONote.NF (rawNoteDecode x) := fun x hx => hn x (List.mem_cons_of_mem c hx)
    simp only [originalQuadraticRemainder,List.head?_cons,Option.some.injEq,List.tail_cons,Bool.and_eq_true,decide_eq_true_eq,List.map_cons,List.cons.injEq]
    rw [normal_code_finite_eq c 2 hc,code_list_ones l hl]
    constructor
    · rintro ⟨h,hlist⟩
      exact ⟨l.length,h,hlist⟩
    · rintro ⟨n,h,hlist⟩
      have hlen := congrArg List.length hlist
      simp only [List.length_map,List.length_replicate] at hlen
      exact ⟨h,by simpa only [hlen] using hlist⟩

 theorem original_leading_code_correct (delta : NONote) (hd : delta.1.repr ≠ 0) :
    ONote.NF (rawNoteDecode (originalLeadingCode (rawNoteEncode delta.1))) ∧
    (rawNoteDecode (originalLeadingCode (rawNoteEncode delta.1))).repr=Ordinal.log Ordinal.omega0 delta.1.repr := by
  obtain ⟨l,hl⟩ := original_units_head delta.1.repr (normalRepresentationSound delta) hd
  have hc := originalUnitCodeCorrect delta
  cases he : originalUnitCodes (rawNoteEncode delta.1) with
  | nil => simp only [he,List.map_nil,hl] at hc
  | cons c cs =>
    have hn := hc.2 c (by rw [he]; exact List.mem_cons_self)
    have hmap : (rawNoteDecode c).repr=Ordinal.log Ordinal.omega0 delta.1.repr := by
      have h := hc.1
      rw [he,List.map_cons,hl] at h
      exact (List.cons.inj h).1
    simpa only [originalLeadingCode,he,List.headD_cons] using And.intro hn hmap

end LogicLineages.PermittedControl
