module
public import LogicLineages.PermittedControl.ActualZeroClassConcreteAssemblyTargets
import LogicLineages.PermittedControl.ActualRankedRowColumnsWeightsProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationWeightsProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassConcreteAssembly
open OrdinalComparison FieldComparison PreparedProjection
open ActualZeroClassReplacement ActualRankedRowColumns ActualWeightedReadNormalization
open ActualCountOriginDispositions ActualZeroClassCohortTransfer
open SelectedNonlinearImageBounds (NonlinearField)

private theorem groupAppend (xs ys : List Read) :
    groupedWeights (xs ++ ys) = groupedWeights xs + groupedWeights ys := by
  induction xs with
  | nil => simp [groupedWeights]
  | cons rd xs ih =>
      change Finsupp.single rd.1.2 rd.1.1 + groupedWeights (xs ++ ys) =
        (Finsupp.single rd.1.2 rd.1.1 + groupedWeights xs) + groupedWeights ys
      rw [ih,add_assoc]

theorem appendRankedColumns (r : Nat) (constant : Int) (xs ys : List Read) :
    (rankedRow r constant (xs ++ ys)).value =
      (rankedRow r 0 xs).value + (rankedRow r 0 ys).value ∧
    (rankedRow r constant (xs ++ ys)).count =
      (rankedRow r 0 xs).count + (rankedRow r 0 ys).count := by
  have all := exactRankedCoefficients r constant (xs ++ ys)
  have left := exactRankedCoefficients r 0 xs
  have right := exactRankedCoefficients r 0 ys
  constructor
  · apply Finsupp.ext
    intro k
    rw [Finsupp.add_apply]
    by_cases active : NonlinearField k.2
    · rw [all.2.2.1 k active,left.2.2.1 k active,right.2.2.1 k active,groupAppend] <;> rfl
    · rw [all.2.2.2.1 k active,left.2.2.2.1 k active,right.2.2.2.1 k active,zero_add]
  · apply Finsupp.ext
    intro k
    rw [Finsupp.add_apply,all.2.1 k,left.2.1 k,right.2.1 k,groupAppend] <;> rfl

private theorem movedPrefixesCountShape (f : Nat → Nat) (ρ : Nat → Nat)
    (a : SurvivingPrefix) (ps : List SurvivingPrefix) (out : List Read)
    (hm : MovedPrefixes f ρ a ps out) :
    ∀ rd ∈ out, ∃ rank lam mu, rd.1.2 = LowerOperand.count rank lam mu := by
  induction hm with
  | nil => simp
  | same _ _ _ ih =>
      intro rd hrd
      rcases List.mem_cons.mp hrd with rfl | mem
      · exact ⟨a.rank,a.lam,a.eta,rfl⟩
      · exact ih rd mem
  | higher _ _ _ _ ih =>
      intro rd hrd
      rcases List.mem_cons.mp hrd with rfl | mem
      · exact ⟨a.rank,a.lam,a.eta,rfl⟩
      · rcases List.mem_cons.mp mem with rfl | rest
        · exact ⟨_,_,_,rfl⟩
        · exact ih rd rest

theorem movedValueColumnZero (f : Nat → Nat) (ρ : Nat → Nat) (r : Nat)
    (anchor : Option SurvivingPrefix) (ps : List SurvivingPrefix) (out : List Read)
    (hm : MovedAt f ρ anchor ps out) :
    (rankedRow r 0 out).value = 0 := by
  have hshape : ∀ rd ∈ out, ∃ rank lam mu, rd.1.2 = LowerOperand.count rank lam mu := by
    cases anchor with
    | none =>
        obtain ⟨_,rfl⟩ := hm
        simp
    | some a => exact movedPrefixesCountShape f ρ a ps out hm
  have cols := exactRankedCoefficients r 0 out
  apply Finsupp.ext
  intro k
  change (rankedRow r 0 out).value k = 0
  by_cases active : NonlinearField k.2
  · rw [cols.2.2.1 k active]
    by_contra nonzero
    obtain ⟨rd,member,key⟩ :=
      (exactGroupedWeights out (valueOperand r k)).2.2 (Finsupp.mem_support_iff.mpr nonzero)
    obtain ⟨rank,lam,mu,count⟩ := hshape rd member
    have bad : LowerOperand.count rank lam mu = LowerOperand.ordinary k.1 k.2 :=
      count.symm.trans key
    cases bad
  · exact cols.2.2.2.1 k active

end LogicLineages.PermittedControl.ActualZeroClassConcreteAssembly
