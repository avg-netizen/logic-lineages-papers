module
public import LogicLineages.OrdinalComparison.TerminationOrdering.TypedObservationAccessTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.TypedObservationAccessProof
open Source Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains ExecutableDomainBottom TypedObservationAccess

theorem trueCalibration : TypedObservationAccessTargets.TrueCalibration := by
  intro Symbol inst arity I τ P strict a o
  by_cases h : Accepted I τ P o
  · simp only [readBit,dif_pos h]
    exact ⟨fun ht => ⟨h,ht⟩,fun ⟨_,ht⟩ => ht⟩
  · simp only [readBit,dif_neg h,Bool.false_eq_true,exists_prop]
    exact ⟨False.elim,fun ⟨ha,_⟩ => h ha⟩

theorem rejectedFalse : TypedObservationAccessTargets.RejectedFalse := by
  intro Symbol inst arity I τ P strict a o h
  exact dif_neg h

theorem typedCoordinate : TypedObservationAccessTargets.TypedCoordinate := by
  intro Symbol inst arity I τ P strict a Q o
  rcases Q with ⟨⟨ports,hports⟩,hPQ⟩
  rcases o with ⟨⟨ports',σ,body⟩,ho,he,hσ⟩
  dsimp at he hσ ⊢
  subst ports'
  subst σ
  have h : Accepted I τ P ⟨ports,τ,body⟩ := ⟨hports,hPQ,rfl,ho⟩
  rw [readBit,dif_pos h]
  rfl

theorem readMonotone : TypedObservationAccessTargets.ReadMonotone := by
  intro Symbol inst arity I τ P strict a b o hab
  have hv := (RecursiveNaturalDomainsProof.transportOrder (family I τ)
    (NaturalTupleLayerProof.layerFamily I τ (lower I τ)) (familyEquation I τ) P a b).mp hab
  change layerView I τ P a ≤ layerView I τ P b at hv
  by_cases h : Accepted I τ P o
  · simp only [readBit,dif_pos h,acceptedCoordinate,coordinate]
    cases strict
    · exact ((hv.1 _).2.1 _)
    · exact ((hv.1 _).2.2 _)
  · simp only [readBit,dif_neg h,le_refl]

theorem restrictionAccess : TypedObservationAccessTargets.RestrictionAccess := by
  intro Symbol inst arity I τ P strict Q h a o hQo
  have iffA : Accepted I τ P o ↔ Accepted I τ Q o := by
    constructor
    · intro hp; exact ⟨hp.1,hQo,hp.2.2⟩
    · intro hq; exact ⟨hq.1,(fun p hp => hQo p (h p hp)),hq.2.2⟩
  by_cases hp : Accepted I τ P o
  · have hq := iffA.mp hp
    simp only [readBit,dif_pos hp,dif_pos hq,acceptedCoordinate,coordinate,
      RecursiveNaturalDomainsProof.layerViewWeaken]
    rfl
  · have hq : ¬ Accepted I τ Q o := fun hq => hp (iffA.mpr hq)
    simp only [readBit,dif_neg hp,dif_neg hq]

theorem bottomFalse : TypedObservationAccessTargets.BottomFalse := by
  intro Symbol inst arity I τ P strict o
  by_cases h : Accepted I τ P o
  · simp only [readBit,dif_pos h,acceptedCoordinate,coordinate,
      ExecutableDomainBottomProof.allBitsFalse Symbol inst arity I τ P]
    cases strict <;> rfl
  · exact dif_neg h

end LogicLineages.OrdinalComparison.TerminationOrdering.TypedObservationAccessProof
