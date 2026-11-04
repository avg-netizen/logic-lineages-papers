module
public import LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectCertificatesTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectCertificatesProof
open Source QuotientDirectCertificates DirectMultisetPresentation

theorem directSoundness : QuotientDirectCertificatesTargets.ActualDirectCertificateSoundness := by
  intro n arity symbols S Gamma table source target c h
  obtain ⟨⟨hs,ht,hn⟩,hd⟩ := by simpa [directTest] using h
  exact ⟨c.1.1,c.1.2.1,c.1.2.2,hs,ht,hn,
    (QuotientDominationCertificatesProof.dominationCertificates n arity symbols S Gamma table c.1.2.1 c.1.2.2).mp ⟨c.2,hd⟩⟩

theorem directCertificates : QuotientDirectCertificatesTargets.ActualDirectCertificates := by
  intro n arity symbols S Gamma table source target
  constructor
  · rintro ⟨c,h⟩
    exact directSoundness n arity symbols S Gamma table source target c h
  · rintro ⟨kept,removed,inserted,hs,ht,hn,hd⟩
    obtain ⟨entries,he⟩ := (QuotientDominationCertificatesProof.dominationCertificates n arity symbols S Gamma table removed inserted).mpr hd
    exact ⟨((kept,removed,inserted),entries),by simp [directTest,hs,ht,hn,he]⟩

theorem numericDirectCertificates : QuotientDirectCertificatesTargets.ActualNumericDirectCertificates := by
  intro n arity symbols S Gamma table source target
  constructor
  · rintro ⟨c,h⟩
    cases hs : Encodable.decode (α := List Nat) source with
    | none => simp only [numericTest,hs,Option.any_none,Bool.false_eq_true] at h
    | some ss =>
      cases ht : Encodable.decode (α := List Nat) target with
      | none => simp only [numericTest,hs,ht,Option.any_some,Option.any_none,Bool.false_eq_true] at h
      | some ts =>
        cases hc : Encodable.decode (α := Certificate) c with
        | none => simp only [numericTest,hs,ht,hc,Option.any_some,Option.any_none,Bool.false_eq_true] at h
        | some certificate =>
          refine ⟨ss,ts,rfl,rfl,?_⟩
          apply directSoundness n arity symbols S Gamma table ss ts certificate
          simpa only [numericTest,hs,ht,hc,Option.any_some] using h
  · rintro ⟨ss,ts,hs,ht,hd⟩
    obtain ⟨certificate,hc⟩ := (directCertificates n arity symbols S Gamma table ss ts).mpr hd
    exact ⟨Encodable.encode certificate,by simpa only [numericTest,hs,ht,Encodable.encodek,Option.any_some] using hc⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectCertificatesProof
