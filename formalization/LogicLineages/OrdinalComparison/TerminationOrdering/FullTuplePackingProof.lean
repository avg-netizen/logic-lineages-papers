module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FullTuplePackingTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FullTuplePackingProof
open Source FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets TypedExtraAppend FullTuplePacking

theorem typeClosure : FullTuplePackingTargets.TypeClosure := by
  intro Symbol inst arity I τ s
  exact ⟨fun i => (argumentTag I τ s i).property,(resultTag I τ s).property⟩

theorem exactLength : FullTuplePackingTargets.ExactLength := by
  intro Symbol inst arity I τ s P v
  simp only [packTuple,List.length_ofFn]

theorem exactEntry : FullTuplePackingTargets.ExactEntry := by
  intro Symbol inst arity I τ s P v i
  simp [packTuple]

theorem membership : FullTuplePackingTargets.Membership := by
  intro Symbol inst arity I τ s P v p
  simp only [packTuple,List.mem_ofFn]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i,hi.symm⟩
  · rintro ⟨i,hi⟩
    exact ⟨i,hi.symm⟩

theorem pointwiseDomination : FullTuplePackingTargets.PointwiseDomination := by
  intro Symbol inst arity I τ s P v w hvw p hp
  obtain ⟨i,rfl⟩ := (membership Symbol inst arity I τ s P v p).mp hp
  refine ⟨⟨argumentTag I τ s i,w i⟩,?_,?_⟩
  · exact (membership Symbol inst arity I τ s P w _).mpr ⟨i,rfl⟩
  · exact (TypedExtraDownsetsProof.packedSame _ _ _).mpr (hvw i)

theorem weakeningMap : FullTuplePackingTargets.WeakeningMap := by
  intro Symbol inst arity I τ s P Q h v
  simp only [packTuple,List.map_ofFn]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.FullTuplePackingProof
