module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FiniteObservationBitsTargets
public import LogicLineages.OrdinalComparison.SourcePortContextsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FiniteObservationBitsProof
open Source Source.SourceTypeSupport Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits

theorem worldCalibration : FiniteObservationBitsTargets.WorldCalibration := by
  intro Symbol arity I P
  have he := Source.SourcePortContextsProof.portContextEnumeration (budget I) (literalTypes I.source++literalTypes I.target) P
  simpa only [worldList,List.toFinset_append,Source.SourcePortContextsProof.literalTypeEnumeration Symbol arity I.context I.sourceType I.source,
    Source.SourcePortContextsProof.literalTypeEnumeration Symbol arity I.context I.targetType I.target] using he

theorem observationCalibration : FiniteObservationBitsTargets.ObservationCalibration := by
  intro Symbol arity I τ P o
  exact o.property

theorem exhaustiveEnumeration : FiniteObservationBitsTargets.ExhaustiveEnumeration := by
  intro Symbol inst arity I τ P a
  exact Finset.mem_univ a

theorem weakeningIdentity : FiniteObservationBitsTargets.WeakeningIdentity := by
  intro Symbol arity I τ P a
  rfl

theorem weakeningComposition : FiniteObservationBitsTargets.WeakeningComposition := by
  intro Symbol arity I τ P Q R h k a
  rfl

theorem weakeningSuprema : FiniteObservationBitsTargets.WeakeningSuprema := by
  intro Symbol arity I τ P Q h S
  funext R
  change (sSup S) ⟨R.val,fun p hp => R.property p (h p hp)⟩ = (sSup (weaken h '' S)) R
  rw [sSup_apply_eq_sSup_image,sSup_apply_eq_sSup_image,Set.image_image]
  rfl

theorem weakeningInfima : FiniteObservationBitsTargets.WeakeningInfima := by
  intro Symbol arity I τ P Q h S
  funext R
  change (sInf S) ⟨R.val,fun p hp => R.property p (h p hp)⟩ = (sInf (weaken h '' S)) R
  rw [sInf_apply_eq_sInf_image,sInf_apply_eq_sInf_image,Set.image_image]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.FiniteObservationBitsProof
