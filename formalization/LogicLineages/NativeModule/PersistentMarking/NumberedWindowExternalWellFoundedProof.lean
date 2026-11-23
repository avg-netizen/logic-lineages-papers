module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalWellFoundedTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowStructuralComputabilityChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowFixedConfinedSimulationChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationRealizationProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowExternalWellFoundedProof
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowOrdinaryTranslation
open NumberedWindowArithmeticLeastClass NumberedWindowSimulationData NumberedWindowExternalWellFoundedTargets

theorem positive : ActualPositiveRelationWellFounded := by
  intro S K Γ τ hk
  constructor
  intro q
  obtain ⟨i,hi⟩ := (NumberedWindowPathWitnessChecks.exact_ActualClassCodeFibers S K Γ τ hk).1 q
  exact (NumberedWindowExternalApplicationChecks.exact_ScalarClassAccessibility S K Γ τ hk q i hi).1
    (NumberedWindowStructuralComputabilityChecks.exact_EveryActualAddressInExternalI S K Γ τ hk q i hi)

def FixedSimulation (S : Signature) (K : List Ty) : Prop :=
  ∀ s t, ConfinedPair.Strict S s t → (∀ a ∈ TypeSupport.support s, a ∈ K) →
    ∃ Q T, tr s = some Q ∧ tr t = some T ∧
      ∃ hs : InWindow S K Spine.EmptyContext s.type Q, ∃ ht : InWindow S K Spine.EmptyContext s.type T,
        RS S K Spine.EmptyContext s.type (classOf ⟨Q,hs⟩) (classOf ⟨T,ht⟩)

private theorem pullback {S K τ} (sim : FixedSimulation S K)
    (x : Class S K Spine.EmptyContext τ)
    (ac : Acc (fun r q => RS S K Spine.EmptyContext τ q r) x) :
    ∀ s (Q : NTerm) (hs : InWindow S K Spine.EmptyContext τ Q),
      tr s = some Q → classOf ⟨Q,hs⟩ = x → s.type = τ →
      (∀ a ∈ TypeSupport.support s, a ∈ K) → Acc (fun t s => ConfinedPair.Strict S s t) s := by
  induction ac with
  | intro x _ ih =>
    intro s Q hs quoted eq ty contained
    constructor
    intro t edge
    obtain ⟨υ,ps,pt,_,_⟩ := edge.1
    have incl := edge.2.2
    have tt : t.type = τ := (NumberedWindowSimulationRealizationProof.paperType pt).trans
      ((NumberedWindowSimulationRealizationProof.paperType ps).symm.trans ty)
    obtain ⟨Q',T,qs,qt,hw,tW,path⟩ := sim s t edge contained
    cases Option.some.inj (quoted.symm.trans qs)
    cases ty
    exact ih _ (eq ▸ path) t T tW qt rfl tt (fun a ha => contained a (incl a ha))

theorem fromFixed (S : Signature) (sim : ∀ K, DecisionSourceUniverse.Closed K → FixedSimulation S K) :
    WellFounded (fun t s => ConfinedPair.Strict S s t) := by
  constructor
  intro s
  by_cases outgoing : ∃ t, ConfinedPair.Strict S s t
  · obtain ⟨t,step⟩ := outgoing
    obtain ⟨τ,ps,_,ordinary,_⟩ := step.1
    have exactSupport := DecisionInventoryProof.ordinaryExact EmptyContext s τ ps.1 ordinary
    have hk : DecisionSourceUniverse.Closed (TypeSupport.support s) := by
      intro a ha c hc
      exact (exactSupport c).mp (DecisionInventoryProof.auxiliaryClosed s a ((exactSupport a).mpr ha) c hc)
    have start := sim (TypeSupport.support s) hk
    obtain ⟨Q,T,quoted,_,hQ,_,_⟩ := start s t step (fun _ h => h)
    have acc := (positive S (TypeSupport.support s) [] s.type hk).apply (classOf ⟨Q,hQ⟩)
    exact pullback start _ acc s Q hQ quoted rfl rfl (fun _ h => h)
  · exact Acc.intro s (fun t edge => (outgoing ⟨t,edge⟩).elim)

theorem confined : ConfinedStrictWellFounded := fun S =>
  fromFixed S (fun K hk s t edge contained =>
    NumberedWindowFixedConfinedSimulationChecks.exact_PositiveConfinedSimulationInSuppliedWindow
      S K s t hk contained edge)

end LogicLineages.PersistentMarking.NumberedWindowExternalWellFoundedProof
