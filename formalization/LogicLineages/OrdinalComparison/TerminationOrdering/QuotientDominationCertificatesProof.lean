module
public import LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDominationCertificatesTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDominationCertificatesProof
open Source QuotientDominationCertificates DirectMultisetPresentation

theorem occurrenceSoundness : QuotientDominationCertificatesTargets.ActualOccurrenceSoundness := by
  intro n arity symbols S Gamma table removed inserted entries h
  induction inserted generalizing entries with
  | nil =>
    cases entries with
    | nil => exact ⟨rfl, .nil⟩
    | cons entry entries => simp [test] at h
  | cons y ys ih =>
    cases entries with
    | nil => simp [test] at h
    | cons entry entries =>
      rcases entry with ⟨index,certificate⟩
      cases hi : removed[index]? with
      | none => simp [test,hi] at h
      | some z =>
        obtain ⟨hp,ht⟩ := by simpa [test,hi] using h
        obtain ⟨hlen,hw⟩ := ih entries ht
        have hr : relation n arity symbols S Gamma table z y :=
          (NumberedQuotientPathCertificatesProof.numericPositivePathCertificates n arity symbols S Gamma table z y).mp ⟨certificate,hp⟩
        exact ⟨by simp [hlen], .cons ⟨z,hi,hr⟩ hw⟩

theorem witnessCompletion : QuotientDominationCertificatesTargets.ActualWitnessCompletion := by
  intro n arity symbols S Gamma table removed inserted indices hw
  induction hw with
  | nil => exact ⟨[],rfl,rfl⟩
  | @cons y index ys indices hhead htail ih =>
    obtain ⟨z,hi,hr⟩ := hhead
    obtain ⟨certificate,hp⟩ :=
      (NumberedQuotientPathCertificatesProof.numericPositivePathCertificates n arity symbols S Gamma table z y).mpr hr
    obtain ⟨entries,he,ht⟩ := ih
    refine ⟨(index,certificate)::entries,by simp [he],?_⟩
    simp [test,hi,hp,ht]

theorem dominationCertificates : QuotientDominationCertificatesTargets.ActualDominationCertificates := by
  intro n arity symbols S Gamma table removed inserted
  constructor
  · rintro ⟨entries,h⟩
    obtain ⟨hlen,hw⟩ := occurrenceSoundness n arity symbols S Gamma table removed inserted entries h
    exact (DirectMultisetPresentationProof.occurrenceWitnesses Nat
      (relation n arity symbols S Gamma table) removed inserted).mpr
      ⟨entries.map Prod.fst,by simpa using hlen,hw⟩
  · intro h
    obtain ⟨indices,_,hw⟩ := (DirectMultisetPresentationProof.occurrenceWitnesses Nat
      (relation n arity symbols S Gamma table) removed inserted).mp h
    obtain ⟨entries,_,ht⟩ := witnessCompletion n arity symbols S Gamma table removed inserted indices hw
    exact ⟨entries,ht⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDominationCertificatesProof
