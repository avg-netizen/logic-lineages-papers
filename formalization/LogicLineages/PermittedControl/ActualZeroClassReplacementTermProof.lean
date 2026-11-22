module
public import LogicLineages.PermittedControl.ActualZeroClassReplacementTargets
import LogicLineages.PermittedControl.ActualZeroClassReplacementPrefixProof
import LogicLineages.PermittedControl.SelectedCountOnlyClassProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassReplacement
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum
open SelectedCountOnlyClass (prefixTarget prefixNotationExact)

theorem exactOccurrenceReplacement (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (C : Nat) (t : WeightedOperand) (v : Nat) (ann : Annotation)
    (actual : LowerOperandActual f ρ t.2 v)
    (read : lowerOperandRead f ρ t.2 = some (some v))
    (annotation : ActualAnnotation f ρ t v ann)
    (ready : PrefixTailReady f B ρ C t ann) :
    let out := replaceOccurrence f C t v ann
    liftedReads f ρ out.1.toList ∧ out.2 + readSum out.1.toList = (contribution f C t v ann).2 := by
  cases ann with
  | zeroWeight =>
      exact ⟨True.intro,rfl⟩
  | linear =>
      exact ⟨⟨actual,read,True.intro⟩,by simp [replaceOccurrence,contribution,readSum,actualSum]⟩
  | ordinary q =>
      by_cases same : f q = C
      · simp only [replaceOccurrence,contribution,if_pos same]
        exact ⟨True.intro,rfl⟩
      · simp only [replaceOccurrence,contribution,if_neg same]
        exact ⟨⟨actual,read,True.intro⟩,by simp [readSum,actualSum]⟩
  | count i q κ =>
      by_cases same : f q = C
      · obtain ⟨_,rank,lam,mu,op,below,first,_⟩ := annotation
        have etaRepr : (prefixTarget mu).1.repr = mu.1.repr + Ordinal.omega0 ^ (2 : Ordinal.{0}) :=
          prefixNotationExact.2 mu
        have paid := exactPrefixRead f ρ rank lam mu v i
          (op ▸ actual) (by simpa only [etaRepr] using below) (by simpa only [etaRepr] using first)
        by_cases identity : i = 0
        · simp only [replaceOccurrence,contribution,if_pos same,op,if_pos identity]
          exact ⟨True.intro,by simp [readSum,actualSum,identity]⟩
        · obtain ⟨prefixActual,prefixRead⟩ := paid.2 identity
          by_cases long : shortGapLength lam (prefixTarget mu) = 0
          · simp only [replaceOccurrence,contribution,if_pos same,op,if_neg identity,if_pos long]
            refine ⟨⟨prefixActual,prefixRead,True.intro⟩,?_⟩
            simp [readSum,actualSum,mul_add,add_comm]
          · have positive := Nat.pos_of_ne_zero long
            simp only [PrefixTailReady,op] at ready
            have count := exactShortPrefix f B selected ρ rank lam (prefixTarget mu) i prefixActual positive
              (ready same identity positive)
            simp only [replaceOccurrence,contribution,if_pos same,op,if_neg identity,if_neg long]
            refine ⟨True.intro,?_⟩
            simp [readSum,actualSum,mul_add,count,add_comm]
      · simp only [replaceOccurrence,contribution,if_neg same]
        exact ⟨⟨actual,read,True.intro⟩,by simp [readSum,actualSum]⟩

end LogicLineages.PermittedControl.ActualZeroClassReplacement
