import LogicLineages.PersistentMarking.NumberedWindowFixedConfinedSimulationTargets
import LogicLineages.PersistentMarking.NumberedWindowSimulationConfinedProof

namespace LogicLineages.PersistentMarking.NumberedWindowFixedConfinedSimulationProof
open LiteralDerivationTree
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowOrdinaryTranslation
open NumberedWindowSimulationData NumberedWindowFixedConfinedSimulationTargets

private theorem admissible {S K q τ} (hq : Spine.PaperTerm S q τ) (ho : Spine.Ordinary q)
    (hSupport : ∀ ρ ∈ TypeSupport.support q, ρ ∈ K) : SymbolicAdmissible K q :=
  fun ρ hρ => hSupport ρ ((DecisionInventoryProof.ordinaryExact Spine.EmptyContext q τ hq.1 ho ρ).mp hρ)

theorem quote : OrdinaryQuoteInSuppliedWindow := by
  intro S K q τ hq ho hSupport
  obtain ⟨Q, hQ⟩ := (NumberedWindowOrdinaryDomainProof.termDomain q).mpr ho
  have hRep := ((NumberedWindowOrdinaryQuoteProof.term q Q hQ).2 0).1
  exact ⟨Q, hQ, NumberedWindowRealizationWindowProof.inWindow S K Spine.EmptyContext τ 0 q Q
    hq.1 hq.2 (admissible hq ho hSupport) hRep⟩

theorem positive : PositiveConfinedSimulationInSuppliedWindow := by
  intro S K s t hk hSupport h
  obtain ⟨⟨τ, hs, ht, hos, hot⟩, hStrict, hIncluded⟩ := h
  obtain ⟨d⟩ := (LiteralDerivationLocalityChecks.exact_CertificateExact S (.strict s t)).mp hStrict
  obtain ⟨Q, hQ⟩ := (NumberedWindowOrdinaryDomainProof.termDomain s).mpr hos
  let budget := NumberedWindowSimulationData.budget d
  have hRep := ((NumberedWindowOrdinaryQuoteProof.term s Q hQ).2 budget).1
  have hsWindow := admissible hs hos hSupport
  have htWindow := admissible ht hot (fun ρ hr => hSupport ρ (hIncluded ρ hr))
  obtain ⟨T, hT, trace, hAdm, hPositive⟩ := NumberedWindowSimulationFinishProof.strict
    S K s t d hk hsWindow htWindow budget Q (Nat.le_refl _) hRep
  obtain ⟨hSource, hTarget, hPath⟩ := NumberedWindowSimulationQuotientProof.positive
    S K Spine.EmptyContext s.type Q T trace hAdm hPositive
  exact ⟨Q, T, hQ, hT, hSource, hTarget, hPath⟩

end LogicLineages.PersistentMarking.NumberedWindowFixedConfinedSimulationProof
