module
public import LogicLineages.PermittedControl.ActualRankedNormalizationSyntaxTargets
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRankedNormalizationSyntax
open scoped Classical
open PreparedProjection
open MixedSameRankResidue (WeightedOperand)
open ActualZeroClassReplacement (Read liftedReads)
open ActualWeightedReadNormalization (groupedWeights normalizeReads exactNormalizedReads)

private theorem sameWeights (reads : List Read) :
    groupedWeights reads = syntaxWeights (reads.map Prod.fst) := by
  induction reads with
  | nil => rfl
  | cons rd reads ih =>
      change Finsupp.single rd.1.2 rd.1.1 + groupedWeights reads =
        Finsupp.single rd.1.2 rd.1.1 + syntaxWeights (reads.map Prod.fst)
      rw [ih]

private theorem sourceWeight (terms : List WeightedOperand) (op : LowerOperand)
    (active : op ∈ (syntaxWeights terms).support) :
    ∃ t ∈ terms, t.2 = op := by
  induction terms with
  | nil => simp [syntaxWeights] at active
  | cons t terms next =>
      by_cases same : t.2 = op
      · exact ⟨t,List.mem_cons_self,same⟩
      · have nonzero := Finsupp.mem_support_iff.mp active
        have rest : syntaxWeights terms op ≠ 0 := by
          simpa only [syntaxWeights,Finsupp.add_apply,Finsupp.single_apply,if_neg same,zero_add]
            using nonzero
        obtain ⟨u,hu,eq⟩ := next (Finsupp.mem_support_iff.mpr rest)
        exact ⟨u,List.mem_cons_of_mem _ hu,eq⟩

theorem exactNormalizedTermSkeleton : ExactNormalizedTermSkeleton := by
  constructor
  · intro f ρ source xs result
    have live : liftedReads f ρ source := by
      by_contra missing
      have absent := (exactNormalizedReads f ρ source).1.mpr missing
      rw [result] at absent
      cases absent
    obtain ⟨ys,normal,keys,_,_,_,data⟩ := (exactNormalizedReads f ρ source).2 live
    have same := Option.some.inj (result.symm.trans normal)
    subst ys
    let weight := groupedWeights source
    let attach : LowerOperand → WeightedOperand := fun op => (weight op,op)
    have signed : xs.map Prod.fst = (xs.map (fun rd => rd.1.2)).map attach := by
      simp only [List.map_map,Function.comp_apply]
      apply List.map_congr_left
      intro rd used
      have coeff := (data rd used).1
      change rd.1 = (groupedWeights source rd.1.2,rd.1.2)
      exact Prod.ext coeff rfl
    rw [signed,keys]
    simp only [attach,weight,normalizedTerms,sameWeights source]
  · intro terms t used
    obtain ⟨op,listed,rfl⟩ := List.mem_map.mp used
    have h : op ∈ (syntaxWeights terms).support := Finset.mem_toList.mp listed
    exact ⟨Finsupp.mem_support_iff.mp h,sourceWeight terms op h⟩

end LogicLineages.PermittedControl.ActualRankedNormalizationSyntax
