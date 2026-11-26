module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationFinishProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationQuotientProof
public import LogicLineages.NativeModule.PersistentMarking.LiteralDerivationLocalityChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationConfinedProof
open LiteralDerivationTree
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowOrdinaryTranslation
open NumberedWindowSimulationData NumberedWindowSimulationJobs
open NumberedWindowPositiveSimulationTargets
open TypeSupport (support)

theorem confined : ConfinedOrdinarySimulation := by
  intro S s t h
  obtain ⟨⟨τ,hs,ht,hos,hot⟩,hStrict,hIncluded⟩ := h
  obtain ⟨d⟩ :=
    (LiteralDerivationLocalityChecks.exact_CertificateExact S (.strict s t)).mp hStrict
  obtain ⟨Q,hQuote⟩ := (NumberedWindowOrdinaryDomainProof.termDomain s).mpr hos
  let b := budget d
  have hQ := ((NumberedWindowOrdinaryQuoteProof.term s Q hQuote).2 b).1
  have hS := DecisionInventoryProof.ordinaryExact E s τ hs.1 hos
  have hT := DecisionInventoryProof.ordinaryExact E t τ ht.1 hot
  have hK : DecisionSourceUniverse.Closed (support s) := by
    intro a ha c hc
    exact (hS c).mp (DecisionInventoryProof.auxiliaryClosed s a ((hS a).mpr ha) c hc)
  have hsK : SymbolicAdmissible (support s) s := fun a ha => (hS a).mp ha
  have htK : SymbolicAdmissible (support s) t := fun a ha => hIncluded a ((hT a).mp ha)
  obtain ⟨T,hQuoteT,path,hAdm,hPos⟩ := NumberedWindowSimulationFinishProof.strict
    S (support s) s t d hK hsK htK b Q (Nat.le_refl _) hQ
  obtain ⟨hSource,hDest,hPath⟩ := NumberedWindowSimulationQuotientProof.positive
    S (support s) E s.type Q T path hAdm hPos
  exact ⟨Q,T,hQuote,hQuoteT,hSource,hDest,hPath⟩

end LogicLineages.PersistentMarking.NumberedWindowSimulationConfinedProof
