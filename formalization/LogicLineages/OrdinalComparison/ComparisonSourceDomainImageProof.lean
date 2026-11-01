module
public import LogicLineages.OrdinalComparison.ComparisonSourceDomainProgramProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonSourceDomain

private theorem raw_positive (n : Nat) (hne : n≠0) : 0<(rawNoteDecode n).repr := by
  cases hd : rawNoteDecode n with
  | zero =>
    have h := rawNoteEncodeDecode n
    rw [hd] at h
    change 0=n at h
    exact (hne h.symm).elim
  | oadd e c t => exact ONote.oadd_pos e c t

private theorem typed_word (word : List (Nat × Nat)) (hv : comparisonRawKernelEntriesValid word) :
    ∃ w : List (NONote × Nat), encodePrincipalKernelWord (comparisonRawWord w)=word ∧
      ∀ p∈w,0<p.1.1.repr := by
  induction word with
  | nil => exact ⟨[],rfl,by intro p h; cases h⟩
  | cons p word ih =>
    have hp := hv p (by simp)
    have ht : comparisonRawKernelEntriesValid word := fun q hq => hv q (List.mem_cons_of_mem p hq)
    obtain ⟨w,hw,hpos⟩ := ih ht
    let eta : NONote := ⟨rawNoteDecode p.1,(rawNormalDecodeCorrect p.1).mp hp.1⟩
    have hcode : rawNoteEncode eta.1=p.1 := by simpa only [eta] using rawNoteEncodeDecode p.1
    have hpositive : 0<eta.1.repr := raw_positive p.1 hp.2
    refine ⟨(eta,p.2)::w,?_,?_⟩
    · change (rawNoteEncode eta.1,p.2)::encodePrincipalKernelWord (comparisonRawWord w)=p::word
      rw [hcode,hw]
    · intro q hq
      rcases List.mem_cons.mp hq with h | h
      · subst q; exact hpositive
      · exact hpos q h

theorem image : Targets.ComparisonSourceDomainImage := by
  intro n
  constructor
  · intro hv
    have hmod : n%2<2 := Nat.mod_lt _ (by decide)
    have hsum := Nat.mod_add_div n 2
    by_cases h0 : n%2=0
    · have hp : (encodedPositiveSourceData (n/2)).1=1 := by
        simpa only [encodedComparisonSourceDomain,if_pos h0] using hv
      obtain ⟨E,hcode,hvalid⟩ := (PositiveSourceDomain.data_image (n/2)).mp hp
      refine ⟨.positive E,?_,hvalid⟩
      change 2*positiveExprEncode E=n
      rw [hcode]
      omega
    · let p := (n/2).unpair
      let word := (Encodable.decode (α := List (Nat × Nat)) p.1).getD []
      have hg : word≠[] ∧ Encodable.encode word=p.1 ∧ comparisonRawKernelEntriesValid word ∧
          (encodedPositiveSourceData p.2).1=1 ∧ (encodedPositiveSourceData p.2).2=1 := by
        rw [encodedComparisonSourceDomain,if_neg h0] at hv
        exact (PositiveSourceDomain.flag_correct _).mp hv
      obtain ⟨w,hword,hpositive⟩ := typed_word word hg.2.2.1
      obtain ⟨E,hcode,hvalid⟩ := (PositiveSourceDomain.data_image p.2).mp hg.2.2.2.1
      have hopen : positiveExprHasInput E=true := by
        have hi := hg.2.2.2.2
        rw [← hcode,(PositiveSourceDomain.data_program.2 E).2] at hi
        exact (PositiveSourceDomain.flag_correct _).mp hi
      have hnonempty : w≠[] := by
        intro h
        apply hg.1
        rw [← hword,h]
        rfl
      refine ⟨.range w E,?_,hnonempty,hpositive,hvalid,hopen⟩
      change 2*Nat.pair (Encodable.encode (encodePrincipalKernelWord (comparisonRawWord w)))
        (positiveExprEncode E)+1=n
      rw [hword,hg.2.1,hcode,Nat.pair_unpair]
      omega
  · rintro ⟨E,hcode,hvalid⟩
    rw [← hcode]
    exact correct E hvalid

end LogicLineages.OrdinalComparison.ComparisonSourceDomain
