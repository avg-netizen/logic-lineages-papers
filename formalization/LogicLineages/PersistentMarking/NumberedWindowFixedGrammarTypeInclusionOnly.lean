import LogicLineages.PersistentMarking.NumberedWindowArithmeticScalarTargets

namespace LogicLineages.PersistentMarking.NumberedWindowFixedGrammarTypeInclusionOnly
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowArithmeticTyCode (encodeTy)

/-- Exactly the fixed-settings inclusion, with only the original legacy
settings import. No physical-guard or internal-calculus import is needed for
this fact about the two original lists. -/
def ExactFixedGrammarTypeInclusion : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty) (n : Nat),
    n ∈ (fixed S K).window.1 → n ∈ (fixed S K).types

theorem exact_FixedGrammarTypeInclusion : ExactFixedGrammarTypeInclusion := by
  intro S K n h
  change n ∈ (K.filter _).map encodeTy at h
  change n ∈ K.map encodeTy
  rcases List.mem_map.mp h with ⟨a, ha, eq⟩
  exact List.mem_map.mpr ⟨a, (List.mem_filter.mp ha).1, eq⟩

#print axioms exact_FixedGrammarTypeInclusion

end LogicLineages.PersistentMarking.NumberedWindowFixedGrammarTypeInclusionOnly
