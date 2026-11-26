module
public import LogicLineages.PermittedControl.ActualCountOriginDispositionsTargets
import LogicLineages.PermittedControl.ActualZeroClassReplacementPrefixProof
import LogicLineages.PermittedControl.SelectedCountOnlyClassProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCountOriginDispositions
open OrdinalComparison FieldComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement ActualZeroClassCohortTransfer
open SelectedCountOnlyClass (prefixTarget prefixNotationExact)

theorem headDisposition (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (C : Nat) (entry : Origin) (anchor : Option SurvivingPrefix)
    (ps : List SurvivingPrefix) (out : List Read)
    (paid : OriginPaid f B ρ C entry)
    (moved : MovedAt f ρ anchor ((survivingPrefix f C entry.1.1 entry.2).toList ++ ps) out)
    (reads : liftedReads f ρ out) :
    ∃ (d : CountDisposition) (first tail : List Read),
      out = first ++ tail ∧ OriginOutcome f ρ anchor entry d first ∧
      MovedAt f ρ anchor ps tail ∧ liftedReads f ρ tail := by
  obtain ⟨⟨⟨weight,op⟩,v⟩,ann⟩ := entry
  obtain ⟨actual,_,annotation,key,ready,kind⟩ := paid
  cases ann with
  | zeroWeight => cases kind
  | linear => cases kind
  | ordinary q => cases kind
  | count i q κ =>
      obtain ⟨_,rank,lam,mu,source,below,first,_⟩ := annotation
      change op = LowerOperand.count rank lam mu at source
      subst op
      have same : f q = C := Option.some.inj key
      have repr := prefixNotationExact.2 mu
      have prefixFacts := exactPrefixRead f ρ rank lam mu v i actual
        (by simpa only [repr] using below) (by simpa only [repr] using first)
      by_cases identity : i = 0
      · have absent : survivingPrefix f C (weight,.count rank lam mu) (.count i q κ) = none := by
          simp [survivingPrefix,identity]
        simp only [absent,Option.toList_none,List.nil_append] at moved
        refine ⟨.ended κ,[],out,rfl,⟨True.intro,?_⟩,moved,reads⟩
        simp only [if_pos identity]
        exact ⟨prefixFacts.1.mp identity,rfl,rfl⟩
      · obtain ⟨actualPrefix,encodedPrefix⟩ := prefixFacts.2 identity
        by_cases long : shortGapLength lam (prefixTarget mu) = 0
        · let head : SurvivingPrefix := ⟨rank,lam,prefixTarget mu,weight,i⟩
          have present : survivingPrefix f C (weight,.count rank lam mu) (.count i q κ) = some head := by
            simp [survivingPrefix,same,identity,long,head]
          simp only [present,Option.toList_some,List.cons_append,List.nil_append] at moved
          cases anchor with
          | none => exact False.elim (List.cons_ne_nil _ _ moved.1)
          | some pivot =>
              change MovedPrefixes f ρ pivot (head::ps) out at moved
              cases moved with
              | same rankEqual countEqual tail =>
                  have atSame : rank = pivot.rank := rankEqual
                  refine ⟨.survives κ,[anchorRead pivot weight],_,rfl,
                    ⟨⟨reads.1,reads.2.1,True.intro⟩,?_⟩,tail,reads.2.2⟩
                  simp only [if_neg identity,if_pos long]
                  refine ⟨pivot,rfl,actualPrefix,encodedPrefix,?_⟩
                  rw [if_pos atSame]
                  exact ⟨countEqual,rfl,rfl⟩
              | higher rankLt count middle tail =>
                  have strict : pivot.rank < rank := rankLt
                  have different : rank ≠ pivot.rank := ne_of_gt strict
                  refine ⟨.transferred (some (pivot.lam,pivot.eta + (lam - prefixTarget mu))) κ,
                    [anchorRead pivot weight,subtractRead pivot head _],_,rfl,
                    ⟨⟨reads.1,reads.2.1,reads.2.2.1,reads.2.2.2.1,True.intro⟩,?_⟩,
                    tail,reads.2.2.2.2⟩
                  simp only [if_neg identity,if_pos long]
                  refine ⟨pivot,rfl,actualPrefix,encodedPrefix,?_⟩
                  rw [if_neg different]
                  exact ⟨strict,_,count,middle,rfl,rfl⟩
        · have absent : survivingPrefix f C (weight,.count rank lam mu) (.count i q κ) = none := by
            simp [survivingPrefix,long]
          have positive := Nat.pos_of_ne_zero long
          have shortCount := exactShortPrefix f B selected ρ rank lam (prefixTarget mu) i
            actualPrefix positive (ready same identity positive)
          simp only [absent,Option.toList_none,List.nil_append] at moved
          refine ⟨.ended (κ + (shortGapLength lam (prefixTarget mu) : Int)),[],out,rfl,
            ⟨True.intro,?_⟩,moved,reads⟩
          simp only [if_neg identity,if_neg long]
          exact ⟨shortCount,rfl,rfl⟩

end LogicLineages.PermittedControl.ActualCountOriginDispositions
