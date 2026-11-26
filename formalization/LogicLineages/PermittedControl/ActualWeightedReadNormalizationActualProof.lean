module
public import LogicLineages.PermittedControl.ActualWeightedReadNormalizationTargets
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationWeightsProof
import LogicLineages.PermittedControl.PreparedParameterActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualWeightedReadNormalization
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open ActualZeroClassReplacement

private theorem paidReads (f : Nat → Nat) (ρ : Nat → Nat) (xs : List Read) :
    liftedReads f ρ xs ↔ ∀ r ∈ xs, lowerOperandRead f ρ r.1.2 = some (some r.2) := by
  induction xs with
  | nil => simp [liftedReads,orderedReads]
  | cons r xs next =>
      constructor
      · intro paid p member
        rcases List.mem_cons.mp member with equal | tail
        · subst p
          exact paid.2.1
        · exact next.mp paid.2.2 p tail
      · intro everyone
        have hit := everyone r List.mem_cons_self
        exact ⟨(preparedTiedProjection.1 f ρ r.1.2 r.2).mp hit,hit,
          next.mpr (fun p member => everyone p (List.mem_cons_of_mem _ member))⟩

theorem exactInputChecks : ExactInputChecks := by
  intro f ρ xs
  rw [paidReads f ρ xs]
  simp only [checkedReads,List.all_eq_true,decide_eq_true_eq]

private def renderedRead (weights : LowerOperand →₀ Int) (V : LowerOperand → Nat)
    (op : LowerOperand) : Read := ((weights op,op),V op)

private theorem collectReads (f : Nat → Nat) (ρ : Nat → Nat) (weights : LowerOperand →₀ Int)
    (V : LowerOperand → Nat) (ops : List LowerOperand)
    (reads : ∀ op ∈ ops, lowerOperandRead f ρ op = some (some (V op))) :
    ops.mapM (readAtWeight f ρ weights) = some (ops.map (renderedRead weights V)) := by
  induction ops with
  | nil => rfl
  | cons op ops next =>
      have head := reads op List.mem_cons_self
      have tail := next (fun later member => reads later (List.mem_cons_of_mem _ member))
      have rendered : readAtWeight f ρ weights op = some (renderedRead weights V op) := by
        simp [readAtWeight,head,renderedRead]
      simp [List.mapM_cons,rendered,tail]

private theorem renderedSum (weights : LowerOperand →₀ Int) (V : LowerOperand → Nat)
    (ops : List LowerOperand) :
    readSum (ops.map (renderedRead weights V)) = (ops.map (fun op => weights op * (V op : Int))).sum := by
  induction ops with
  | nil => rfl
  | cons op ops next =>
      change weights op * (V op : Int) + readSum (ops.map (renderedRead weights V)) =
        weights op * (V op : Int) + (ops.map (fun next => weights next * (V next : Int))).sum
      rw [next]

theorem exactNormalizedReads : ExactNormalizedReads := by
  intro f ρ xs
  let weights := groupedWeights xs
  let V (op : LowerOperand) : Nat := (lowerOperandRead f ρ op).join.getD 0
  have success (paid : liftedReads f ρ xs) :
      normalizeReads f ρ xs = some (weights.support.toList.map (renderedRead weights V)) := by
    have original := (paidReads f ρ xs).mp paid
    have surviving (op : LowerOperand) (member : op ∈ weights.support.toList) :
        lowerOperandRead f ρ op = some (some (V op)) := by
      obtain ⟨prior,wasRead,key⟩ :=
        (exactGroupedWeights xs op).2.2 (Finset.mem_toList.mp member)
      have literal := original prior wasRead
      rw [key] at literal
      simp [V,literal]
    have calibrated := (exactInputChecks f ρ xs).mpr paid
    simp only [normalizeReads,calibrated,if_true]
    exact collectReads f ρ weights V weights.support.toList surviving
  constructor
  · constructor
    · intro failure paid
      rw [success paid] at failure
      cases failure
    · intro unpaid
      have wrong : checkedReads f ρ xs = false := by
        cases checked : checkedReads f ρ xs with
        | false => rfl
        | true => exact False.elim (unpaid ((exactInputChecks f ρ xs).mp checked))
      simp [normalizeReads,wrong]
  · intro paid
    let ys := weights.support.toList.map (renderedRead weights V)
    have original := (paidReads f ρ xs).mp paid
    have valueOf (r : Read) (member : r ∈ xs) : V r.1.2 = r.2 := by
      simp [V,original r member]
    have priorRead (op : LowerOperand) (member : op ∈ weights.support) :
        ∃ r ∈ xs, r.1.2 = op ∧ r.2 = V op := by
      obtain ⟨r,member,key⟩ := (exactGroupedWeights xs op).2.2 member
      exact ⟨r,member,key,by simpa only [key] using (valueOf r member).symm⟩
    have keys : ys.map (fun r => r.1.2) = weights.support.toList := by
      simp only [ys,List.map_map,Function.comp_def,renderedRead,List.map_id_fun',id_eq]
    refine ⟨ys,success paid,keys,keys.symm ▸ Finset.nodup_toList _,?_,?_,?_⟩
    · apply (paidReads f ρ ys).mpr
      intro r member
      obtain ⟨op,inKeys,equal⟩ := List.mem_map.mp member
      subst r
      obtain ⟨prior,wasRead,key,sameValue⟩ := priorRead op (Finset.mem_toList.mp inKeys)
      have actual := original prior wasRead
      rw [key,sameValue] at actual
      exact actual
    · calc
        readSum xs = weights.sum (fun op a => a * (V op : Int)) :=
          (evaluateGrouped V xs valueOf).symm
        _ = (weights.support.toList.map (fun op => weights op * (V op : Int))).sum :=
          (Finset.sum_map_toList _ _).symm
        _ = readSum ys := (renderedSum weights V _).symm
    · intro r member
      obtain ⟨op,inKeys,equal⟩ := List.mem_map.mp member
      subst r
      have support := Finset.mem_toList.mp inKeys
      exact ⟨rfl,Finsupp.mem_support_iff.mp support,priorRead op support⟩

end LogicLineages.PermittedControl.ActualWeightedReadNormalization
