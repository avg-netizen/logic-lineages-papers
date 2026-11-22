module
public import LogicLineages.PermittedControl.ActualZeroClassCohortTransferTargets
import LogicLineages.PermittedControl.ActualZeroClassReplacementPrefixProof
import LogicLineages.PermittedControl.SelectedCountOnlyClassProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassCohortTransfer
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement
open SelectedCountOnlyClass (prefixTarget prefixNotationExact)

private theorem actualSurvivor (f : Nat → Nat) (ρ : Nat → Nat) (C : Nat)
    (t : WeightedOperand) (v : Nat) (ann : Annotation) (p : SurvivingPrefix)
    (actual : LowerOperandActual f ρ t.2 v) (annotation : ActualAnnotation f ρ t v ann)
    (found : survivingPrefix f C t ann = some p) :
    ActualPrefix f ρ C p ∧ (replaceOccurrence f C t v ann).1 = some p.asRead := by
  cases ann with
  | zeroWeight => cases found
  | linear => cases found
  | ordinary q => cases found
  | count i q κ =>
      obtain ⟨weight,rank,lam,mu,op,below,first,endpoint,_⟩ := annotation
      have etaRepr : (prefixTarget mu).1.repr = mu.1.repr + Ordinal.omega0 ^ (2 : Ordinal.{0}) :=
        prefixNotationExact.2 mu
      by_cases keep : f q = C ∧ i ≠ 0 ∧ shortGapLength lam (prefixTarget mu) = 0
      · simp only [survivingPrefix,op,if_pos keep,Option.some.injEq] at found
        subst p
        obtain ⟨same,nonzero,long⟩ := keep
        have paid := exactPrefixRead f ρ rank lam mu v i (op ▸ actual)
          (by simpa only [etaRepr] using below) (by simpa only [etaRepr] using first)
        obtain ⟨newActual,newRead⟩ := paid.2 nonzero
        have sameKey : f (entryNormAt f (countInitial lam.1.repr (ρ rank)) i) = C :=
          (congrArg f endpoint).symm.trans same
        refine ⟨⟨weight,Nat.pos_of_ne_zero nonzero,long,⟨newActual,newRead,True.intro⟩,sameKey⟩,?_⟩
        simp only [replaceOccurrence,op,if_pos same,if_neg nonzero,if_pos long,SurvivingPrefix.asRead]
      · simp only [survivingPrefix,op,if_neg keep] at found
        cases found

theorem exactCohort : ExactCohort := by
  refine ⟨actualSurvivor,?_⟩
  intro f ρ C terms values annotations aligned
  induction aligned with
  | nil => simp [cohort]
  | @cons t terms v values ann annotations actual _ annotation _ next =>
      intro p member
      rw [cohort] at member
      rcases List.mem_append.mp member with head | tail
      · cases out : survivingPrefix f C t ann with
        | none => simp [out] at head
        | some current =>
            have eq : p = current := by simpa only [out,Option.toList_some,List.mem_singleton] using head
            subst p
            exact (actualSurvivor f ρ C t v ann current actual annotation out).1
      · exact next p tail

end LogicLineages.PermittedControl.ActualZeroClassCohortTransfer
