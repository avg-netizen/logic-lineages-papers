module

public import LogicLineages.NativeModule.PersistentMarking.CutStrictStrictProof
public import LogicLineages.NativeModule.PersistentMarking.CutStrictWeakProof

@[expose] public section

namespace LogicLineages.PersistentMarking.CutOccurrenceProof
theorem fullOccurrences : CutOccurrenceTargets.FullOccurrences :=
  ⟨CutMatchingProof.weakWeak,CutWeakStrictProof.weakStrict,CutStrictWeakProof.strictWeak,CutStrictStrictProof.strictStrict⟩
end LogicLineages.PersistentMarking.CutOccurrenceProof
