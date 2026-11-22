module
public import LogicLineages.PermittedControl.ActualZeroClassConcreteAssemblyTargets
import LogicLineages.PermittedControl.ActualZeroClassCohortTransferMinimumProof
import LogicLineages.PermittedControl.ActualZeroClassCohortTransferProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassConcreteAssembly
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement ActualWeightedReadNormalization
open ActualRankedRowColumns ActualRankedZeroClass ActualZeroClassCohortTransfer
open ActualCountOriginDispositions ActualZeroClassGroupedMovedCount
open SelectedCountOnlyClass (prefixTarget)

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
          · simp only [survivingPrefix,if_neg keep,Option.none_ne_some] at found

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

theorem chooseFiniteAnchor (f : Nat → Nat) (ρ : Nat → Nat) (C r : Nat)
    (raw xs : List Read) (annotations : List Annotation)
    (paid : liftedReads f ρ raw) (bounded : ∀ rd ∈ raw, rd.1.2.rank < r)
    (normalized : normalizeReads f ρ raw = some xs)
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
      obtain ⟨out,hout,_,_,_,_,weights⟩ := (exactNormalizedReads f ρ raw).2 paid
      have equal : out = xs := Option.some.inj (hout.symm.trans normalized)
      subst out
      have b : ∀ t ∈ xs.map Prod.fst, t.2.rank < r := by
        intro t ht
        obtain ⟨rd,hrd,hr⟩ := List.mem_map.mp ht
        subst t
        obtain ⟨prior,hprior,hkey,_⟩ := (weights rd hrd).2.2
        calc
          rd.1.2.rank = prior.1.2.rank := (congrArg LowerOperand.rank hkey).symm
          _ < r := bounded prior hprior
      have ar := cohortRankBound f C r (xs.map Prod.fst) annotations b a member
      refine ⟨⟨a.rank,ar⟩,(a.lam,a.eta),?_⟩
      intro anchor equal
      cases equal
      exact ⟨rfl,rfl⟩

theorem chooseMovedReads (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (ordered : StrictMono ρ) (C : Nat) (xs : List Read)
    (annotations : List Annotation)
    (aligned : AlignedAnnotations f ρ (xs.map Prod.fst) (xs.map Prod.snd) annotations)
    (tails : TransferReady B ρ (cohort f C (xs.map Prod.fst) annotations)) :
    let ps := cohort f C (xs.map Prod.fst) annotations
    ∃ moved : List Read, MovedAt f ρ (leastPrefix ps) ps moved ∧ liftedReads f ρ moved := by
  let ps := cohort f C (xs.map Prod.fst) annotations
  have transfer := exactCohortTransfer f B hf ρ ordered C (xs.map Prod.fst) (xs.map Prod.snd)
    annotations aligned tails
  change (match leastPrefix ps with
    | none => ps = []
    | some a => a ∈ ps ∧ (∀ p ∈ ps, a.rank ≤ p.rank) ∧
        ∃ out, MovedPrefixes f ρ a ps out ∧ liftedReads f ρ out ∧
          readSum (ps.map SurvivingPrefix.asRead) = readSum out ∧
          ∀ rd ∈ out, rd.1.2.rank = a.rank) at transfer
  change ∃ moved : List Read, MovedAt f ρ (leastPrefix ps) ps moved ∧ liftedReads f ρ moved
  cases h : leastPrefix ps with
  | none =>
      have empty : ps = [] := by simpa only [h] using transfer
      exact ⟨[],⟨empty,rfl⟩,True.intro⟩
  | some a =>
      have moved : ∃ out, MovedPrefixes f ρ a ps out ∧ liftedReads f ρ out ∧
          readSum (ps.map SurvivingPrefix.asRead) = readSum out ∧
          ∀ rd ∈ out, rd.1.2.rank = a.rank := by
        have real : a ∈ ps ∧ (∀ p ∈ ps, a.rank ≤ p.rank) ∧
            ∃ out, MovedPrefixes f ρ a ps out ∧ liftedReads f ρ out ∧
              readSum (ps.map SurvivingPrefix.asRead) = readSum out ∧
              ∀ rd ∈ out, rd.1.2.rank = a.rank := by
          simpa only [h] using transfer
        exact real.2.2
      obtain ⟨out,hm,hr,_,_⟩ := moved
      exact ⟨out,hm,hr⟩

end LogicLineages.PermittedControl.ActualZeroClassConcreteAssembly
