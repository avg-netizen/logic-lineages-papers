module
public import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingTargets
import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingEncodingProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationWeightsProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalOperandGrouping
open scoped Classical
open PreparedProjection MixedSameRankResidue ActualZeroClassReplacement
open ActualWeightedReadNormalization

theorem firstKeyMem {α : Type} [DecidableEq α] (keys : List α) (key : α) :
    key ∈ firstKeys keys ↔ key ∈ keys := by
  simp only [firstKeys,List.mem_reverse,List.mem_dedup]

theorem firstKeyNodup {α : Type} [DecidableEq α] (keys : List α) :
    (firstKeys keys).Nodup := by
  exact (List.nodup_dedup keys.reverse).reverse

private theorem firstKeyCode (keys : List LowerOperand) :
    firstKeys (keys.map LowerOperand.code) = (firstKeys keys).map LowerOperand.code := by
  simp only [firstKeys,List.map_reverse,
    List.dedup_map_of_injective exactOperandEncoding.1]

private theorem exactSignedWeight (terms : List WeightedOperand) (key : LowerOperand) :
    signedWeight (terms.map encodeTerm) key.code = signedWeight terms key := by
  induction terms with
  | nil => rfl
  | cons t terms ih =>
      change (if t.2.code = key.code then t.1 else 0) +
          signedWeight (terms.map encodeTerm) key.code =
        (if t.2 = key then t.1 else 0) + signedWeight terms key
      by_cases same : t.2 = key
      · rw [if_pos same,if_pos (congrArg LowerOperand.code same),ih]
      · have rawNe : t.2.code ≠ key.code := fun h => same (exactOperandEncoding.1 h)
        rw [if_neg same,if_neg rawNe,ih]

private theorem packLiteral (terms : List WeightedOperand) (keys : List LowerOperand) :
    (((keys.map (fun key => (signedWeight terms key,key))).filter
        (fun t => decide (t.1 ≠ 0))).map encodeTerm) =
      (((keys.map LowerOperand.code).map
        (fun key => (signedWeight (terms.map encodeTerm) key,key))).filter
          (fun t => decide (t.1 ≠ 0))) := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
      simp only [List.map_cons,List.filter_cons,exactSignedWeight]
      split <;> simp_all only [List.map_cons,encodeTerm]

private theorem literal (terms : List WeightedOperand) :
    (groupTyped terms).map encodeTerm = groupRaw (terms.map encodeTerm) := by
  unfold groupTyped groupRaw groupTape
  have keys : (terms.map encodeTerm).map Prod.snd = (terms.map Prod.snd).map LowerOperand.code :=
    by simp only [List.map_map] <;> rfl
  rw [keys,firstKeyCode]
  exact packLiteral terms _

private theorem chosenKeys (terms : List WeightedOperand) (keys : List LowerOperand)
    (different : keys.Nodup) :
    ((((keys.map (fun key => (signedWeight terms key,key))).filter
        (fun t => decide (t.1 ≠ 0))).map Prod.snd)).Nodup := by
  induction keys with
  | nil => exact List.nodup_nil
  | cons key keys ih =>
      have tails := List.nodup_cons.mp different
      simp only [List.map_cons,List.filter_cons]
      split
      · rw [List.map_cons,List.nodup_cons]
        refine ⟨?_, ih tails.2⟩
        intro used
        obtain ⟨pair,listed,identified⟩ := List.mem_map.mp used
        obtain ⟨original,present,record⟩ := List.mem_map.mp (List.mem_filter.mp listed).1
        have same : original = key := (congrArg Prod.snd record).trans identified
        exact tails.1 (same ▸ present)
      · exact ih tails.2

private theorem signedReads (xs : List Read) (key : LowerOperand) :
    signedWeight (xs.map Prod.fst) key = groupedWeights xs key := by
  rw [(exactGroupedWeights xs key).1]
  simp only [signedWeight,List.map_map,Function.comp_apply,weightAt]

private theorem present (xs : List Read) (w : Int) (key : LowerOperand) :
    (w,key) ∈ groupTyped (xs.map Prod.fst) ↔
      w = groupedWeights xs key ∧ key ∈ (groupedWeights xs).support := by
  constructor
  · intro member
    have bits := List.mem_filter.mp member
    obtain ⟨op,used,eq⟩ := List.mem_map.mp bits.1
    have k : op = key := congrArg Prod.snd eq
    have coeff : signedWeight (xs.map Prod.fst) op = w := congrArg Prod.fst eq
    subst op
    rw [signedReads] at coeff
    exact ⟨coeff.symm,Finsupp.mem_support_iff.mpr
      (coeff.symm ▸ (of_decide_eq_true bits.2 : w ≠ 0))⟩
  · rintro ⟨rfl,active⟩
    refine List.mem_filter.mpr ⟨?_,decide_eq_true (Finsupp.mem_support_iff.mp active)⟩
    apply List.mem_map.mpr
    obtain ⟨rd,used,keyEq⟩ := (exactGroupedWeights xs key).2.2 active
    refine ⟨key,(firstKeyMem _ _).mpr ?_,?_⟩
    · exact List.mem_map.mpr ⟨rd.1,List.mem_map.mpr ⟨rd,used,rfl⟩,keyEq⟩
    · exact Prod.ext (signedReads xs key) rfl

theorem exactCanonicalTape : ExactCanonicalTape := by
  exact ⟨literal,fun terms => chosenKeys terms _ (firstKeyNodup _),present⟩

end LogicLineages.PermittedControl.ActualCanonicalOperandGrouping
