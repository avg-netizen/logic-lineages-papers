module
public import LogicLineages.PersistentMarking.NumberedWindowFixedGrammarTypeTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowFixedGrammarType
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowAdmissionTargets (window)
open NumberedWindowArithmeticTyCode (encodeTy)
open NumberedWindowInternalAuxWindowMemoTargets (typeGuard)

theorem inclusion : ExactFixedGrammarTypeInclusion := by
  intro S K n h
  change n ∈ (K.filter _).map encodeTy at h
  change n ∈ K.map encodeTy
  rcases List.mem_map.mp h with ⟨a, ha, eq⟩
  exact List.mem_map.mpr ⟨a, (List.mem_filter.mp ha).1, eq⟩

theorem guardRun : ExactFixedGuardRunGrammarType := by
  intro S K T cal n h
  rw [cal] at h
  have accepted : typeGuard (fixed S K) n = true := by
    cases hguard : typeGuard (fixed S K) n <;> simp_all
  have inWindow : (fixed S K).window.1.contains n = true :=
    (Bool.and_eq_true.mp accepted).2
  exact inclusion S K n (List.contains_iff_mem.mp inWindow)

end LogicLineages.PersistentMarking.NumberedWindowFixedGrammarType
