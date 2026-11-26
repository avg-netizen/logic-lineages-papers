module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineStrictTargets
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineInputProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineStrictInputProof
open Spine DecisionPorts DecisionObservations FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineEnvironment ProtectedSpineLaws ProtectedSpineStrictTargets

theorem literalStrict (E : Environment) (Γ Δ : Context) (σ : Ty) (x : Nat) (t : Expr)
    (hw : WellFormed E.types E.ports Γ) (hd : WellFormed E.types E.ports Δ) (he : Extends Γ Δ)
    (ht : t ∈ observations E.names E.ports Δ E.target σ) :
    (decode E σ Γ (literalCode E Γ σ x)).strict Δ t = false :=
  (((HereditaryEncodeDecodeProof.encodeDecode E σ Γ _ hw
      (MarkedConstructorLiteralProof.literalValid E σ Γ x)).2 Δ hd he).2.1 t ht).2

theorem bottomStrict (E : Environment) (Γ Δ : Context) (σ : Ty) (t : Expr)
    (hw : WellFormed E.types E.ports Γ) (hd : WellFormed E.types E.ports Δ) (he : Extends Γ Δ)
    (ht : t ∈ observations E.names E.ports Δ E.target σ) :
    (decode E σ Γ (StructuralActions.bottom E σ Γ)).strict Δ t = false :=
  (((StructuralWholeBottomProof.wholeBottom E σ Γ hw).2 Δ hd he).2.1 t ht).2

theorem empty (E : Environment) (Γ : Context) (hw : WellFormed E.types E.ports Γ) :
    StrictlessInputs E Γ ⟨[],[]⟩ := by
  intro Δ hd he σ t ht
  constructor
  · intro x
    exact literalStrict E Γ Δ σ x t hw hd he ht
  · intro i
    have heq : boundCode E Γ [] σ i = StructuralActions.bottom E σ Γ := by
      simp [boundCode,lookupBound]
    change (decode E σ Γ (boundCode E Γ [] σ i)).strict Δ t = false
    rw [heq]
    exact bottomStrict E Γ Δ σ t hw hd he ht

theorem weaken (E : Environment) (Γ Δ : Context) (a : Assignments)
    (ha : InputValid E Γ a) (hs : StrictlessInputs E Γ a)
    (hd : WellFormed E.types E.ports Δ) (he : Extends Γ Δ) :
    StrictlessInputs E Δ (a.restrict E Γ Δ) := by
  intro Θ ht hf σ t hobs
  have he' := DecisionPortsProof.extensionTrans Γ Δ Θ he hf
  have hbits := hs Θ ht he' σ t hobs
  constructor
  · intro x
    have hres := (ProtectedSpineEnvironmentNaturalProof.lookupWeakening
      E Γ Δ a.free a.bound σ x 0 ha.1 hd he ha.2.1 ha.2.2).1
    have hcar := ProtectedSpineEnvironmentLookupProof.freeLookup E Γ a.free σ x ha.1 ha.2.1
    have hr := (HereditaryRestrictionProof.restriction E σ Γ Δ ha.1 hd he _ hcar).2
    rw [hres] at hr
    exact ((hr Θ ht hf).2.1 t hobs).2.trans (hbits.1 x)
  · intro i
    have hres := (ProtectedSpineEnvironmentNaturalProof.lookupWeakening
      E Γ Δ a.free a.bound σ 0 i ha.1 hd he ha.2.1 ha.2.2).2
    have hcar := ProtectedSpineEnvironmentLookupProof.boundLookup E Γ a.bound σ i ha.1 ha.2.2
    have hr := (HereditaryRestrictionProof.restriction E σ Γ Δ ha.1 hd he _ hcar).2
    rw [hres] at hr
    exact ((hr Θ ht hf).2.1 t hobs).2.trans (hbits.2 i)

theorem push (E : Environment) (Γ : Context) (a : Assignments) (α : Ty) (x : Nat)
    (hw : WellFormed E.types E.ports Γ) (hs : StrictlessInputs E Γ a) :
    StrictlessInputs E Γ (a.push α (literalCode E Γ α x)) := by
  intro Δ hd he σ t ht
  have hb := hs Δ hd he σ t ht
  refine ⟨hb.1,?_⟩
  intro i
  cases i with
  | zero =>
    by_cases h : α = σ
    · subst σ
      simpa [boundCode,lookupBound,Assignments.push] using literalStrict E Γ Δ α x t hw hd he ht
    · simpa [boundCode,lookupBound,Assignments.push,h] using bottomStrict E Γ Δ σ t hw hd he ht
  | succ i => simpa [boundCode,lookupBound,Assignments.push] using hb.2 i

end LogicLineages.PersistentMarking.ProtectedSpineStrictInputProof
