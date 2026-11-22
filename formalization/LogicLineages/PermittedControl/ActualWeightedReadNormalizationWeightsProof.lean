module
public import LogicLineages.PermittedControl.ActualWeightedReadNormalizationTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualWeightedReadNormalization
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open ActualZeroClassReplacement

private theorem groupedWeight (xs : List Read) (op : LowerOperand) :
    groupedWeights xs op = (xs.map (weightAt op)).sum := by
  classical
  induction xs with
  | nil => rfl
  | cons r xs next =>
      simp only [groupedWeights,Finsupp.add_apply,Finsupp.single_apply,List.map_cons,
        List.sum_cons,weightAt,next]

private theorem supportOccurs (xs : List Read) (op : LowerOperand)
    (inSupport : op ∈ (groupedWeights xs).support) : ∃ r ∈ xs, r.1.2 = op := by
  classical
  induction xs with
  | nil => simpa [groupedWeights] using inSupport
  | cons r xs next =>
      by_cases same : r.1.2 = op
      · exact ⟨r,List.mem_cons_self,same⟩
      · have nonzero := Finsupp.mem_support_iff.mp inSupport
        have tailNonzero : groupedWeights xs op ≠ 0 := by
          simpa only [groupedWeights,Finsupp.add_apply,Finsupp.single_apply,if_neg same,zero_add]
            using nonzero
        obtain ⟨prior,member,key⟩ := next (Finsupp.mem_support_iff.mpr tailNonzero)
        exact ⟨prior,List.mem_cons_of_mem _ member,key⟩

theorem exactGroupedWeights : ExactGroupedWeights := by
  intro xs op
  refine ⟨groupedWeight xs op,?_,supportOccurs xs op⟩
  rw [← groupedWeight xs op]
  exact Finsupp.mem_support_iff

theorem evaluateGrouped (V : LowerOperand → Nat) (xs : List Read)
    (values : ∀ r ∈ xs, V r.1.2 = r.2) :
    (groupedWeights xs).sum (fun op a => a * (V op : Int)) = readSum xs := by
  classical
  induction xs with
  | nil => simp [groupedWeights,readSum,actualSum]
  | cons r xs next =>
      change (Finsupp.single r.1.2 r.1.1 + groupedWeights xs).sum
          (fun op a => a * (V op : Int)) = r.1.1 * (r.2 : Int) + readSum xs
      rw [Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _),
        Finsupp.sum_single_index (zero_mul _),values r List.mem_cons_self,
        next (fun prior member => values prior (List.mem_cons_of_mem _ member))]

end LogicLineages.PermittedControl.ActualWeightedReadNormalization
