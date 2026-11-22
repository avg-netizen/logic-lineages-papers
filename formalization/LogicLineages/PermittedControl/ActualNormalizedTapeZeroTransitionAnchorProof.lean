module
public import LogicLineages.PermittedControl.ActualNormalizedTapeZeroTransitionTargets
import LogicLineages.PermittedControl.ActualZeroClassCohortTransferMinimumProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNormalizedTapeZeroTransition
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement ActualWeightedReadNormalization
open ActualRankedRowColumns ActualRankedZeroClass ActualZeroClassCohortTransfer
open ActualCountOriginDispositions ActualZeroClassGroupedMovedCount
open SelectedCountOnlyClass (prefixTarget)
open ActualNormalizedTape ActualZeroClassGroupedMovedCount

private theorem survivingRank (f : Nat → Nat) (C : Nat) (t : WeightedOperand)
    (ann : Annotation) (p : SurvivingPrefix) (found : survivingPrefix f C t ann = some p) :
    p.rank = t.2.rank := by
  obtain ⟨weight,op⟩ := t
  cases ann with
  | zeroWeight => cases found
  | linear => cases found
  | ordinary q => cases found
  | count i q κ =>
      cases op with
      | coordinate rank => cases found
      | ordinary rank F => cases found
      | count rank lam mu =>
          by_cases keep : f q = C ∧ i ≠ 0 ∧ shortGapLength lam (prefixTarget mu) = 0
          · simp only [survivingPrefix,if_pos keep,Option.some.injEq] at found
            subst p
            rfl
          · simp only [survivingPrefix,if_neg keep] at found
            cases found

private theorem cohortRankBound (f : Nat → Nat) (C r : Nat) (terms : List WeightedOperand)
    (annotations : List Annotation) (bounded : ∀ t ∈ terms, t.2.rank < r) :
    ∀ p ∈ cohort f C terms annotations, p.rank < r := by
  induction terms generalizing annotations with
  | nil => simp [cohort]
  | cons t terms ih =>
      cases annotations with
      | nil => simp [cohort]
      | cons ann annotations =>
          intro p member
          change p ∈ (survivingPrefix f C t ann).toList ++ cohort f C terms annotations at member
          rcases List.mem_append.mp member with front | back
          · rw [survivingRank f C t ann p (Option.mem_toList.mp front)]
            exact bounded t List.mem_cons_self
          · exact ih annotations (fun s hs => bounded s (List.mem_cons_of_mem _ hs)) p back

theorem chooseTapeFiniteAnchor (f : Nat → Nat) (ρ : Nat → Nat) (C r : Nat)
    (raw xs : List Read) (annotations : List Annotation)
    (bounded : ∀ rd ∈ raw, rd.1.2.rank < r) (tape : NormalizedTape f ρ raw xs)
    (classPresent : (finiteClassColumns r (classReads f C xs annotations)).1.Nonempty ∨
      (finiteClassColumns r (classReads f C xs annotations)).2.Nonempty) :
    ∃ (x₀ : Fin r) (q : NONote × NONote),
      AnchorAt (leastPrefix (cohort f C (xs.map Prod.fst) annotations)) x₀ q := by
  let ps := cohort f C (xs.map Prod.fst) annotations
  change ∃ (x₀ : Fin r) (q : NONote × NONote), AnchorAt (leastPrefix ps) x₀ q
  cases h : leastPrefix ps with
  | none =>
      have hr : Nonempty (Fin r) := by
        rcases classPresent with ⟨k,_⟩ | ⟨k,_⟩
        · exact ⟨k.1⟩
        · exact ⟨k.2⟩
      obtain ⟨x₀⟩ := hr
      refine ⟨x₀,(NONote.ofNat 0,NONote.ofNat 0),?_⟩
      intro a impossible
      cases impossible
  | some a =>
      have member := (exactLeastPrefix.2 ps a h).1
      have b : ∀ t ∈ xs.map Prod.fst, t.2.rank < r := by
        intro t ht
        obtain ⟨rd,hrd,hr⟩ := List.mem_map.mp ht
        subst t
        obtain ⟨prior,hprior,hkey,_⟩ := (tape.records rd hrd).2.2
        calc
          rd.1.2.rank = prior.1.2.rank := (congrArg LowerOperand.rank hkey).symm
          _ < r := bounded prior hprior
      have ar := cohortRankBound f C r (xs.map Prod.fst) annotations b a member
      refine ⟨⟨a.rank,ar⟩,(a.lam,a.eta),?_⟩
      intro anchor equal
      cases equal
      exact ⟨rfl,rfl⟩

end LogicLineages.PermittedControl.ActualNormalizedTapeZeroTransition
