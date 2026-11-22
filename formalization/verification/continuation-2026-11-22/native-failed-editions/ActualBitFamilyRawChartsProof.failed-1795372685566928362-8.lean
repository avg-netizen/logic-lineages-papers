module
public import LogicLineages.PermittedControl.ActualBitFamilyRawChartsTargets
import LogicLineages.PermittedControl.ActualBitFamilyRawLayoutProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesEnumerateProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesCoverageProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesRealizationProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawCharts
open ActualBitFamilyRawLayout (RawFamily names encodeFamily exactRawFamilyNames)
open ActualFiniteOrderBranches (Entry Pattern Dense patterns exactPatternEnumeration actualPattern
  exactActualBranchCoverage exactBranchRealization)
open ActualRankChartPrototype (Consistent)

private theorem consistentOfNoDuplicate (es : List Entry) (uniq : (es.map Prod.fst).Nodup) :
    ∀ a ∈ es, ∀ b ∈ es, a.1 = b.1 → a.2 = b.2 := by
  induction es with
  | nil => simp
  | cons head tail ih =>
      obtain ⟨fresh,limited⟩ : head.1 ∉ tail.map Prod.fst ∧ (tail.map Prod.fst).Nodup :=
        List.nodup_cons.mp uniq
      intro a ha b hb same
      rcases List.mem_cons.mp ha with rfl | aTail <;>
        rcases List.mem_cons.mp hb with rfl | bTail
      · rfl
      · exact (fresh (List.mem_map.mpr ⟨b,bTail,same.symm⟩)).elim
      · exact (fresh (List.mem_map.mpr ⟨a,aTail,same⟩)).elim
      · exact ih limited a aTail b bTail same

theorem exactNonemptyPatterns : ExactNonemptyPatterns := by
  intro source uniq p
  simp only [nonemptyPatterns,List.mem_filter,decide_eq_true_eq,exactPatternEnumeration]
  constructor
  · rintro ⟨dense,pos⟩
    have once : (p.2.map Prod.fst).Nodup := dense.2.1.symm ▸ uniq
    exact ⟨dense,pos,consistentOfNoDuplicate p.2 once⟩
  · rintro ⟨dense,pos,_⟩
    exact ⟨dense,pos⟩

theorem exactRawChartEnumeration : ExactRawChartEnumeration := by
  intro raw p
  exact exactNonemptyPatterns (names raw) (exactRawFamilyNames.1 raw).2.1 p

theorem exactEncodedRawChartCoverage : ExactEncodedRawChartCoverage := by
  intro family pos θ
  let source := names (encodeFamily family)
  let p := actualPattern θ source
  have layout := exactRawFamilyNames.2 family
  obtain ⟨member,ok⟩ := exactActualBranchCoverage θ source
  have dense : Dense source p := (exactPatternEnumeration source p).mp member
  have sourcePos : 0 < source.length := by
    change 0 < (names (encodeFamily family)).length
    rwa [layout.2]
  have pPos : 0 < p.1 := by
    cases hs : source with
    | nil => simp [hs] at sourcePos
    | cons k ks =>
        have inSource : k ∈ source := by rw [hs]; exact List.mem_cons_self
        rw [← dense.2.1] at inSource
        obtain ⟨entry,listed,-⟩ := List.mem_map.mp inSource
        exact Nat.zero_lt_of_lt (dense.2.2.1 entry listed)
  have emits : p ∈ charts (encodeFamily family) := by
    unfold charts nonemptyPatterns
    exact List.mem_filter.mpr ⟨member,decide_eq_true pPos⟩
  obtain ⟨increasing,_,reads⟩ := exactBranchRealization θ source p member ok
  refine ⟨p,emits,ok,dense.1.trans_eq layout.2,increasing,?_⟩
  intro k used
  apply reads
  apply List.mem_toFinset.mp
  rwa [layout.1]

end LogicLineages.PermittedControl.ActualBitFamilyRawCharts
