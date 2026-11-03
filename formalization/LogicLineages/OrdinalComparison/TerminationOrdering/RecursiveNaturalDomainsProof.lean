module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveNaturalDomainsTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveNaturalDomainsProof
open Source FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains

theorem transportRoundTrip {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity}
    (F G : Family I) (h : F=G) (P : World I) (a : F.carrier P) :
    Eq.mp (congrArg (fun D : Family I => D.carrier P) h.symm)
      (Eq.mp (congrArg (fun D : Family I => D.carrier P) h) a)=a := by
  cases h
  rfl

theorem transportOrder {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity}
    (F G : Family I) (h : F=G) (P : World I) (a b : F.carrier P) :
    a ≤ b ↔ Eq.mp (congrArg (fun D : Family I => D.carrier P) h) a ≤
      Eq.mp (congrArg (fun D : Family I => D.carrier P) h) b := by
  cases h
  rfl

theorem transportRestriction {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity}
    (F G : Family I) (h : F=G) (P Q : World I) (k : Extends P Q) (a : F.carrier P) :
    Eq.mp (congrArg (fun D : Family I => D.carrier Q) h) (F.restrict k a)=
      G.restrict k (Eq.mp (congrArg (fun D : Family I => D.carrier P) h) a) := by
  cases h
  rfl

theorem layerFoldView {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (P : World I) (a : Value I τ P) :
    layerFold I τ P (layerView I τ P a)=a :=
  transportRoundTrip _ _ (familyEquation I τ) P a

theorem layerViewFold {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (P : World I) (a : Natural I τ (lower I τ) P) :
    layerView I τ P (layerFold I τ P a)=a :=
  transportRoundTrip _ _ (familyEquation I τ).symm P a

theorem layerViewInjective {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (P : World I) : Function.Injective (layerView I τ P) := by
  intro a b h
  have he := congrArg (layerFold I τ P) h
  simpa only [layerFoldView] using he

theorem layerViewWeaken {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (P Q : World I) (h : Extends P Q) (a : Value I τ P) :
    layerView I τ Q (RecursiveNaturalDomains.weaken h a)=
      ⟨rawWeaken h (layerView I τ P a).val,
        NaturalTupleLayerProof.naturalPreservation Symbol arity I τ (lower I τ) P Q h
          (layerView I τ P a).val (layerView I τ P a).property⟩ :=
  transportRestriction _ _ (familyEquation I τ) P Q h a

theorem exhaustiveEnumeration : RecursiveNaturalDomainsTargets.ExhaustiveEnumeration := by
  intro Symbol inst arity I τ P a
  exact ((family I τ).finite P).complete a

theorem groundRoundTrips : RecursiveNaturalDomainsTargets.GroundRoundTrips := by
  intro Symbol inst arity I P
  constructor
  · intro a
    apply layerViewInjective I .ground P
    simp only [groundFromBits,groundToBits,layerViewFold]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext Q s
      cases s.property
  · intro b
    simp only [groundFromBits,groundToBits,layerViewFold]

theorem groundOrder : RecursiveNaturalDomainsTargets.GroundOrder := by
  intro Symbol inst arity I P a b
  have he := transportOrder _ _ (familyEquation I .ground) P a b
  constructor
  · intro h
    exact (he.mp h).1
  · intro h
    apply he.mpr
    refine ⟨h,?_⟩
    intro Q s
    cases s.property

theorem weakeningIdentity : RecursiveNaturalDomainsTargets.WeakeningIdentity := by
  intro Symbol inst arity I τ P a
  exact (family I τ).restrictIdentity P a

theorem weakeningComposition : RecursiveNaturalDomainsTargets.WeakeningComposition := by
  intro Symbol inst arity I τ P Q R h k a
  exact (family I τ).restrictComposition P Q R h k a

theorem applicationMonotone : RecursiveNaturalDomainsTargets.ApplicationMonotone := by
  intro Symbol inst arity I τ P a s v w h
  exact (layerView I τ P a).property.1 ⟨P,fun _ hp => hp⟩ s v w h

theorem applicationNaturality : RecursiveNaturalDomainsTargets.ApplicationNaturality := by
  intro Symbol inst arity I τ P Q h a s v
  unfold applyValue
  rw [layerViewWeaken]
  exact (layerView I τ P a).property.2 ⟨P,fun _ hp => hp⟩ ⟨Q,h⟩ h s v

end LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveNaturalDomainsProof
