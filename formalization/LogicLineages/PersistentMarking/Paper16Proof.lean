import LogicLineages.PersistentMarking.Paper16Targets
import LogicLineages.PersistentMarking.ComparisonOrdinaryProof
import LogicLineages.PersistentMarking.ElementaryProof
namespace LogicLineages.PersistentMarking.Paper16Proof

theorem elementary : Paper16Targets.Elementary := by
  refine ⟨?_, ElementaryProof.strictIncluded, ElementaryProof.ordinaryReflexive⟩
  intro S q t h
  cases h with
  | inl hw => exact ComparisonOrdinaryProof.weakTargetsOrdinary S q t hw
  | inr hs => exact ComparisonOrdinaryProof.strictTargetsOrdinary S q t hs

end LogicLineages.PersistentMarking.Paper16Proof
