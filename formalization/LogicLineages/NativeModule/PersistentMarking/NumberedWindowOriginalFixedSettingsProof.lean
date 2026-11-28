module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticScalarTargets
public import LogicLineages.PersistentMarking.NumberedWindowRawExchangeSymmetryTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardNumericTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowOriginalFixedSettingsProof

open NumberedWindowAdmissionTargets (typesIn)
open NumberedWindowArithmeticExchangeAtomsTargets (pairs)
open NumberedWindowArithmeticHeadCode (encodeHead)
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowArithmeticTyCode (encodeTy)
open NumberedWindowExchangeAtoms (allowed)
open NumberedWindowHeadEnumerationTargets (admittedHeads equivalentHeads)
open NumberedWindowInternalSettingsGrammarGuardNumericTargets (GrammarTypeInclusion)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)

/-- The grammar uses the same fixed source list before the window filter. -/
theorem exact_FixedGrammarTypeInclusion (S : Spine.Signature) (K : List Ty) :
    GrammarTypeInclusion (fixed S K) := by
  intro n h
  change n ∈ (K.filter _).map encodeTy at h
  change n ∈ K.map encodeTy
  obtain ⟨τ, hτ, same⟩ := List.mem_map.mp h
  exact List.mem_map.mpr ⟨τ, (List.mem_filter.mp hτ).1, same⟩

/-- Every type in a closed source list survives the original window filter. -/
theorem exact_FixedWindowTypeIncluded (S : Spine.Signature) (K : List Ty)
    (closed : DecisionSourceUniverse.Closed K) {n : Nat} (hn : n ∈ K.map encodeTy) :
    n ∈ (fixed S K).window.1 := by
  obtain ⟨τ, hτ, same⟩ := List.mem_map.mp hn
  change n ∈ (K.filter (fun σ => typesIn K (TypeSupport.subtypes σ))).map encodeTy
  refine List.mem_map.mpr ⟨τ, List.mem_filter.mpr ⟨hτ, ?_⟩, same⟩
  apply List.all_eq_true.mpr
  intro σ hσ
  exact decide_eq_true (closed τ hτ σ hσ)

/-- Symmetry holds on the actual numerical table, including all code inputs. -/
theorem exact_FixedHeadPairsSymmetric (S : Spine.Signature) (K : List Ty) :
    HeadPairsSymmetric (fixed S K).equivalentHeads := by
  intro a b
  change allowed (pairs S K) a b = allowed (pairs S K) b a
  have reverse {x y : Nat} (h : allowed (pairs S K) x y = true) :
      allowed (pairs S K) y x = true := by
    have pairMember : (x, y) ∈ pairs S K := of_decide_eq_true h
    obtain ⟨f, hf, rowMember⟩ := List.mem_flatMap.mp pairMember
    obtain ⟨g, hg, same⟩ := List.mem_map.mp rowMember
    obtain ⟨hg, rank⟩ := List.mem_filter.mp hg
    have rankEq : Spine.classRank S f = Spine.classRank S g := of_decide_eq_true rank
    rcases Prod.mk.inj same with ⟨rfl, rfl⟩
    apply decide_eq_true
    exact List.mem_flatMap.mpr
      ⟨g, hg, List.mem_map.mpr ⟨f, List.mem_filter.mpr ⟨hf, decide_eq_true rankEq.symm⟩, rfl⟩⟩
  exact Bool.eq_iff_iff.mpr ⟨reverse, reverse⟩

#print axioms exact_FixedGrammarTypeInclusion
#print axioms exact_FixedWindowTypeIncluded
#print axioms exact_FixedHeadPairsSymmetric

end LogicLineages.PersistentMarking.NumberedWindowOriginalFixedSettingsProof
