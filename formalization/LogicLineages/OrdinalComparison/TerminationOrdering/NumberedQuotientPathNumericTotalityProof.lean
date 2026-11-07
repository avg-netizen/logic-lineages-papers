module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathNumericTotalityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericTotalityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathNumericTotalityProof
open Source NumberedMultisetNumeric NumberedQuotientPathCertificates
open NumberedQuotientPathCertificatesProof ID1Completion.ApplicationCertificateLiftPath

theorem decoderTotality (certificate : Nat) :
    ∃ entries : List EdgeEntry, decodePathCertificate certificate = some entries := by
  obtain ⟨xs, hxs⟩ := NumberedMultisetNumericTotalityProof.decoderTotality certificate
  exact ⟨xs.map Nat.unpair, by simp only [decodePathCertificate, hxs, Option.map_some]⟩

theorem actualPathUniqueDecoding :
    NumberedQuotientPathNumericTotalityTargets.ActualPathUniqueDecoding := by
  intro certificate
  obtain ⟨entries, hentries⟩ := decoderTotality certificate
  refine ⟨entries, hentries, ?_⟩
  intro other hother
  exact Option.some.inj (hother.symm.trans hentries)

/-- The literal fallback in the existing liftPath is never selected by its
path decoder, even for a code rejected by the typed source checker. -/
theorem decoderNeverNone (certificate : Nat) : decodePathCertificate certificate ≠ none := by
  obtain ⟨entries, hentries⟩ := decoderTotality certificate
  rw [hentries]
  simp

theorem decoderReencode (certificate : Nat) :
    pathCertificateNumber ((decodePathCertificate certificate).getD []) = certificate := by
  obtain ⟨xs, hxs⟩ := NumberedMultisetNumericTotalityProof.decoderTotality certificate
  calc
    pathCertificateNumber ((decodePathCertificate certificate).getD []) = numbersNumber xs := by
      simp [decodePathCertificate, hxs, pathCertificateNumber, List.map_map,
        Function.comp_def, Nat.pair_unpair]
    _ = certificate := NumberedMultisetNumericSupportProof.numbersSound certificate xs hxs

theorem actualPathCodingInverse :
    NumberedQuotientPathNumericTotalityTargets.ActualPathCodingInverse :=
  ⟨certificateRoundTrip, decoderReencode⟩

theorem encodingInjective : Function.Injective pathCertificateNumber := by
  intro entries other h
  have he := congrArg decodePathCertificate h
  simpa only [certificateRoundTrip, Option.some.injEq] using he

theorem encodingSurjective : Function.Surjective pathCertificateNumber := by
  intro certificate
  exact ⟨(decodePathCertificate certificate).getD [], decoderReencode certificate⟩

theorem actualPathEncodingBijection :
    NumberedQuotientPathNumericTotalityTargets.ActualPathEncodingBijection :=
  ⟨encodingInjective, encodingSurjective⟩

theorem actualPathDecoderEquation :
    NumberedQuotientPathNumericTotalityTargets.ActualPathDecoderEquation := by
  intro certificate entries
  constructor
  · intro h
    simpa only [h, Option.getD_some] using decoderReencode certificate
  · intro h
    rw [← h]
    exact certificateRoundTrip entries

theorem encodingCons (value edge : Nat) (entries : List EdgeEntry) :
    pathCertificateNumber ((value,edge) :: entries) =
      1 + Nat.pair (Nat.pair value edge) (pathCertificateNumber entries) := rfl

theorem decoderCons (value edge tail : Nat) :
    decodePathCertificate (1 + Nat.pair (Nat.pair value edge) tail) =
      (decodePathCertificate tail).map ((value,edge) :: ·) := by
  obtain ⟨entries, hentries⟩ := decoderTotality tail
  have ht := (actualPathDecoderEquation tail entries).mp hentries
  have hc : pathCertificateNumber ((value,edge) :: entries) =
      1 + Nat.pair (Nat.pair value edge) tail := by
    rw [encodingCons, ht]
  simpa only [hc, hentries, Option.map_some] using certificateRoundTrip ((value,edge) :: entries)

theorem actualPathDecoderStructure :
    NumberedQuotientPathNumericTotalityTargets.ActualPathDecoderStructure :=
  ⟨rfl, decoderCons⟩

theorem decoderZeroIff (certificate : Nat) :
    decodePathCertificate certificate = some [] ↔ certificate = 0 := by
  constructor
  · intro h
    exact ((actualPathDecoderEquation certificate []).mp h).symm
  · intro h
    subst certificate
    rfl

theorem actualLiftPathDecoder :
    NumberedQuotientPathNumericTotalityTargets.ActualLiftPathDecoder := by
  intro n arity Gamma context domain codomain argument certificate
  obtain ⟨entries, hentries⟩ := decoderTotality certificate
  simp only [liftPath, hentries, Option.getD_some, certificateRoundTrip, Option.map_some]

theorem actualLiftPathLength :
    NumberedQuotientPathNumericTotalityTargets.ActualLiftPathLength := by
  intro n arity Gamma context domain codomain argument certificate
  rw [actualLiftPathDecoder]
  obtain ⟨entries, hentries⟩ := decoderTotality certificate
  simp only [hentries, Option.map_some, Option.getD_some, liftEntries, List.length_map]

theorem actualLiftPathEmpty :
    NumberedQuotientPathNumericTotalityTargets.ActualLiftPathEmpty := by
  intro n arity Gamma context domain codomain argument certificate
  have he :
      decodePathCertificate (liftPath n arity Gamma context domain codomain argument certificate) =
        some [] ↔ decodePathCertificate certificate = some [] := by
    rw [actualLiftPathDecoder]
    obtain ⟨entries, hentries⟩ := decoderTotality certificate
    simp only [hentries, Option.map_some, Option.some.injEq, liftEntries, List.map_eq_nil_iff]
  refine ⟨he, ?_⟩
  exact (decoderZeroIff
    (liftPath n arity Gamma context domain codomain argument certificate)).symm.trans
      (he.trans (decoderZeroIff certificate))

theorem actualLiftPathStructure :
    NumberedQuotientPathNumericTotalityTargets.ActualLiftPathStructure := by
  intro n arity Gamma context domain codomain argument
  constructor
  · rfl
  · intro value edge tail
    obtain ⟨entries, hentries⟩ := decoderTotality tail
    have hc := decoderCons value edge tail
    simp only [hentries, Option.map_some] at hc
    simp only [liftPath, hc, hentries, Option.getD_some, liftEntries, List.map_cons, encodingCons]

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathNumericTotalityProof
