module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathCertificatesTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathCertificatesProof
open Source NumberedCopyCertificate NumberedMultisetNumeric NumberedQuotientPaths NumberedNumericQuotientEdge NumberedQuotientPathCertificates

theorem appendTest (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (first : List EdgeEntry) :
    ∀ x y z second,pathTest n arity symbols S Gamma table x y first=true →
      pathTest n arity symbols S Gamma table y z second=true → pathTest n arity symbols S Gamma table x z (first++second)=true := by
  induction first with
  | nil =>
    intro x y z second h1 h2
    have he : x=y := by simpa [pathTest] using h1
    subst y
    exact h2
  | cons entry first ih =>
    obtain ⟨v,c⟩ := entry
    intro x y z second h1 h2
    have hh : numericEdgeTest n arity symbols S Gamma table x v c=true ∧ pathTest n arity symbols S Gamma table v y first=true := by simpa [pathTest] using h1
    have ht := ih v y z second hh.2 h2
    simp [pathTest,hh.1,ht]

theorem pathSound (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (entries : List EdgeEntry) :
    ∀ x y,pathTest n arity symbols S Gamma table x y entries=true → CountedPath (QuotientEdge n arity symbols S (tableAbove table) Gamma) entries.length x y := by
  induction entries with
  | nil =>
    intro x y h
    have he : x=y := by simpa [pathTest] using h
    subst y
    exact .refl x
  | cons entry entries ih =>
    obtain ⟨z,c⟩ := entry
    intro x y h
    have hh : numericEdgeTest n arity symbols S Gamma table x z c=true ∧ pathTest n arity symbols S Gamma table z y entries=true := by simpa [pathTest] using h
    have he := (NumberedNumericQuotientEdgeProof.numericQuotientEdge n arity symbols S Gamma table x z).mp ⟨c,hh.1⟩
    have hp := CountedPath.trans (CountedPath.step he) (ih z y hh.2)
    simpa [Nat.add_comm] using hp

theorem countedPathCertificates : NumberedQuotientPathCertificatesTargets.ActualCountedPathCertificates := by
  intro n arity symbols S Gamma table count x y
  constructor
  · rintro ⟨entries,hl,h⟩
    rw [←hl]
    exact pathSound n arity symbols S Gamma table entries x y h
  · intro h
    induction h with
    | refl x => exact ⟨[],rfl,by simp [pathTest]⟩
    | @step x y h =>
      obtain ⟨c,hc⟩ := (NumberedNumericQuotientEdgeProof.numericQuotientEdge n arity symbols S Gamma table x y).mpr h
      exact ⟨[(y,c)],rfl,by simp [pathTest,hc]⟩
    | trans h1 h2 ih1 ih2 =>
      obtain ⟨first,hfirst,htfirst⟩ := ih1
      obtain ⟨second,hsecond,htsecond⟩ := ih2
      exact ⟨first++second,by simp [hfirst,hsecond],appendTest n arity symbols S Gamma table first _ _ _ second htfirst htsecond⟩

theorem positivePathCertificates : NumberedQuotientPathCertificatesTargets.ActualPositivePathCertificates := by
  intro n arity symbols S Gamma table x y
  constructor
  · rintro ⟨entries,hn,h⟩
    have hl : 0<entries.length := by cases entries <;> simp_all
    exact (NumberedQuotientPathsProof.positiveClosure n arity symbols S (tableAbove table) Gamma x y).mpr
      ⟨entries.length,hl,pathSound n arity symbols S Gamma table entries x y h⟩
  · intro h
    obtain ⟨count,hc,hp⟩ := (NumberedQuotientPathsProof.positiveClosure n arity symbols S (tableAbove table) Gamma x y).mp h
    obtain ⟨entries,hl,ht⟩ := (countedPathCertificates n arity symbols S Gamma table count x y).mpr hp
    refine ⟨entries,?_,ht⟩
    intro he
    simp [he] at hl
    omega

theorem certificateRoundTrip (entries : List EdgeEntry) : decodePathCertificate (pathCertificateNumber entries)=some entries := by
  simp [decodePathCertificate,pathCertificateNumber,NumberedMultisetNumericSupportProof.numbersRoundTrip,List.map_map,Function.comp_def]

theorem numericPositivePathCertificates : NumberedQuotientPathCertificatesTargets.ActualNumericPositivePathCertificates := by
  intro n arity symbols S Gamma table x y
  constructor
  · rintro ⟨certificate,h⟩
    cases hd : decodePathCertificate certificate with
    | none => simp [positivePathTest,hd] at h
    | some entries =>
      cases entries with
      | nil => simp [positivePathTest,hd] at h
      | cons entry rest =>
        have ht : pathTest n arity symbols S Gamma table x y (entry::rest)=true := by simpa [positivePathTest,hd] using h
        exact (positivePathCertificates n arity symbols S Gamma table x y).mp ⟨entry::rest,by simp,ht⟩
  · intro h
    obtain ⟨entries,hn,ht⟩ := (positivePathCertificates n arity symbols S Gamma table x y).mpr h
    cases entries with
    | nil => contradiction
    | cons entry rest =>
      exact ⟨pathCertificateNumber (entry::rest),by simp [positivePathTest,certificateRoundTrip,ht]⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathCertificatesProof
