module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineLawTargets
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineEnvironmentNaturalProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedExtrasRestrictionProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineInputProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode
open ProtectedSpineEnvironment ProtectedSpineLaws

theorem restrictValid (E : Environment) (Γ Δ : Context) (a : Assignments)
    (ha : InputValid E Γ a) (hd : WellFormed E.types E.ports Δ) (he : Extends Γ Δ) :
    InputValid E Δ (a.restrict E Γ Δ) :=
  ⟨hd,ProtectedSpineEnvironmentWeakeningProof.weakening E Γ Δ a.free a.bound ha.1 hd he ha.2.1 ha.2.2⟩

theorem restrictCompose (E : Environment) (Γ Δ Θ : Context) (a : Assignments)
    (ha : InputValid E Γ a) (hd : WellFormed E.types E.ports Δ)
    (ht : WellFormed E.types E.ports Θ) (he : Extends Γ Δ) (hf : Extends Δ Θ) :
    (a.restrict E Γ Δ).restrict E Δ Θ = a.restrict E Γ Θ := by
  obtain ⟨hf',hb⟩ := ProtectedSpineEnvironmentWeakeningProof.composition
    E Γ Δ Θ a.free a.bound ha.1 hd ht he hf ha.2.1 ha.2.2
  unfold Assignments.restrict
  rw [hf',hb]

theorem restrictOrder (E : Environment) (Γ Δ : Context) (a b : Assignments)
    (ha : InputValid E Γ a) (hb : InputValid E Γ b) (hle : InputLE E Γ a b)
    (hd : WellFormed E.types E.ports Δ) (he : Extends Γ Δ) :
    InputLE E Δ (a.restrict E Γ Δ) (b.restrict E Γ Δ) := by
  constructor
  · intro σ x
    have hca := ProtectedSpineEnvironmentLookupProof.freeLookup E Γ a.free σ x ha.1 ha.2.1
    have hcb := ProtectedSpineEnvironmentLookupProof.freeLookup E Γ b.free σ x hb.1 hb.2.1
    have hna := (ProtectedSpineEnvironmentNaturalProof.lookupWeakening
      E Γ Δ a.free a.bound σ x 0 ha.1 hd he ha.2.1 ha.2.2).1
    have hnb := (ProtectedSpineEnvironmentNaturalProof.lookupWeakening
      E Γ Δ b.free b.bound σ x 0 hb.1 hd he hb.2.1 hb.2.2).1
    have h := MarkedExtrasRestrictionProof.codeMonotone E σ Γ Δ ha.1 hd he _ _ hca hcb (hle.1 σ x)
    rw [hna,hnb] at h
    exact h
  · intro σ i
    have hca := ProtectedSpineEnvironmentLookupProof.boundLookup E Γ a.bound σ i ha.1 ha.2.2
    have hcb := ProtectedSpineEnvironmentLookupProof.boundLookup E Γ b.bound σ i hb.1 hb.2.2
    have hna := (ProtectedSpineEnvironmentNaturalProof.lookupWeakening
      E Γ Δ a.free a.bound σ 0 i ha.1 hd he ha.2.1 ha.2.2).2
    have hnb := (ProtectedSpineEnvironmentNaturalProof.lookupWeakening
      E Γ Δ b.free b.bound σ 0 i hb.1 hd he hb.2.1 hb.2.2).2
    have h := MarkedExtrasRestrictionProof.codeMonotone E σ Γ Δ ha.1 hd he _ _ hca hcb (hle.2 σ i)
    rw [hna,hnb] at h
    exact h

theorem pushValid (E : Environment) (Γ : Context) (a : Assignments) (σ : Ty) (c : Code)
    (ha : InputValid E Γ a) (hc : c ∈ (descriptor E σ).carriers Γ) : InputValid E Γ (a.push σ c) :=
  ⟨ha.1,ha.2.1,ProtectedSpineEnvironmentWeakeningProof.pushValid E Γ a.bound σ c ha.2.2 hc⟩

theorem pushOrder (E : Environment) (Γ : Context) (a b : Assignments) (τ : Ty) (c d : Code)
    (hw : WellFormed E.types E.ports Γ) (hab : InputLE E Γ a b)
    (hcd : (descriptor E τ).le Γ c d = true) : InputLE E Γ (a.push τ c) (b.push τ d) := by
  refine ⟨hab.1,?_⟩
  intro σ i
  cases i with
  | zero =>
    by_cases ht : τ = σ
    · subst σ
      simpa [Assignments.push,boundCode,lookupBound] using hcd
    · have hb := (HereditaryPartialOrderProof.partialOrder E σ Γ hw).1 _
        (StructuralWholeBottomProof.wholeBottom E σ Γ hw).1
      simpa [Assignments.push,boundCode,lookupBound,ht] using hb
  | succ i => simpa [Assignments.push,boundCode,lookupBound] using hab.2 σ i

theorem reflexive (E : Environment) (Γ : Context) (a : Assignments) (ha : InputValid E Γ a) :
    InputLE E Γ a a := by
  constructor
  · intro σ x
    exact (HereditaryPartialOrderProof.partialOrder E σ Γ ha.1).1 _
      (ProtectedSpineEnvironmentLookupProof.freeLookup E Γ a.free σ x ha.1 ha.2.1)
  · intro σ i
    exact (HereditaryPartialOrderProof.partialOrder E σ Γ ha.1).1 _
      (ProtectedSpineEnvironmentLookupProof.boundLookup E Γ a.bound σ i ha.1 ha.2.2)

end LogicLineages.PersistentMarking.ProtectedSpineInputProof
