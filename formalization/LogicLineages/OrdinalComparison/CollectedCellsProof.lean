module
public import LogicLineages.OrdinalComparison.CollectedCellsTargets
public import LogicLineages.OrdinalComparison.CollectedRangeCellsProof
public import LogicLineages.OrdinalComparison.SignedCollectedOrientationProof
public import LogicLineages.OrdinalComparison.CollectedFiniteTailProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem finite_peak_maximum {α : Type} (f : α → Nat) (l : List α) (hn : l≠[]) :
    ∃ a∈l, ∀ b∈l, f b≤f a := by
  induction l with
  | nil => exact False.elim (hn rfl)
  | cons a rest ih =>
    by_cases hr : rest=[]
    · subst rest
      refine ⟨a,List.mem_cons_self,?_⟩
      intro b hb
      have h : b=a := by simpa using hb
      rw [h]
    rcases ih hr with ⟨b,hb,hmax⟩
    by_cases hab : f a≤f b
    · refine ⟨b,List.mem_cons_of_mem _ hb,?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hab
      · exact hmax c hc
    · refine ⟨a,List.mem_cons_self,?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact le_rfl
      · exact (hmax c hc).trans (by omega)

private theorem cell_threshold_positive (forms : List CollectedPositiveNF) : 1≤collectedFamilyThreshold forms := by
  induction forms with
  | nil => exact le_rfl
  | cons A forms ih => exact ih.trans (le_max_right _ _)

private theorem cell_threshold_fold_le (forms : List CollectedPositiveNF) (N : Nat) (hN : 1≤N)
    (h : ∀ A∈forms, collectedOneInputThreshold A≤N) : collectedFamilyThreshold forms≤N := by
  induction forms with
  | nil => exact hN
  | cons A forms ih =>
    exact max_le (h A List.mem_cons_self) (ih (fun B hB => h B (List.mem_cons_of_mem A hB)))

private theorem cell_pairwise_strengthen {α : Type} (l : List α) (R S : α → α → Prop)
    (hp : l.Pairwise R) (h : ∀ a∈l, ∀ b∈l, R a b → S a b) : l.Pairwise S := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    have hd := List.pairwise_cons.mp hp
    exact List.pairwise_cons.mpr
      ⟨fun b hb => h a List.mem_cons_self b (List.mem_cons_of_mem a hb) (hd.1 b hb),
        ih hd.2 (fun b hb c hc hr => h b (List.mem_cons_of_mem a hb) c (List.mem_cons_of_mem a hc) hr)⟩

theorem actualCollectedSignedCells : Targets.ActualCollectedSignedCells := by
  refine ⟨encodedCollectedZeroBoundPrimitiveRecursive,?_⟩
  intro forms hv
  dsimp only
  rw [encodedCollectedZeroBoundCorrect forms]
  have hN : 1≤collectedFiniteZeroBound forms :=
    (cell_threshold_positive forms).trans (le_max_left _ _)
  refine ⟨rfl,hN,?_⟩
  intro x hx A hA B hB
  let S := collectedFiniteClosure forms
  have hd := collectedFiniteClosureDomain forms hv
  have hvalid : ∀ C∈S, CollectedPositiveValid C := hd.2.2.1
  have hthreshold : collectedFamilyThreshold S≤collectedFamilyThreshold forms :=
    cell_threshold_fold_le S _ (cell_threshold_positive forms)
      (fun C hC => (collectedClosureBounds forms C hC).2)
  have hsource := fullActualCollectedOneInput.2 S hvalid
  have hSx : encodedCollectedFamilyThreshold (S.map collectedPositiveEncode)≤x := by
    rw [encodedCollectedFamilyThresholdCorrect S]
    exact hthreshold.trans ((le_max_left _ _).trans hx)
  have hpeaks := (hsource.2.2 x hSx).2
  have hMx : max 4 (8*collectedRootCodeBound forms+1)≤x := (le_max_right _ _).trans hx
  cases A with
  | mk c b tags =>
    cases B with
    | mk d e rest =>
      dsimp only [signedCollectedNFRow]
      have hvA : CollectedTagsValid tags := hvalid _ hA
      have hvB : CollectedTagsValid rest := hvalid _ hB
      have hrows := signedCollectedDifferenceValid tags rest hvA hvB
      have hbudget := signedCollectedPairBudget (.mk c b tags) (.mk d e rest)
        (collectedRootCodeBound forms)
        (collectedClosureBounds forms _ hA).1 (collectedClosureBounds forms _ hB).1
      dsimp only [signedCollectedNFRow] at hbudget
      have hvalue := signedCollectedNFRowValue (.mk c b tags) (.mk d e rest) x
      dsimp only [signedCollectedNFRow] at hvalue
      constructor
      · intro hempty
        rw [hempty] at hvalue
        simpa only [actualSignedCollectedValue,List.map_nil,List.sum_nil,add_zero] using hvalue.symm
      · intro hn
        have hentry : ∀ entry∈signedCollectedDifference tags rest,
            entry.1.2∈S ∧ entry.1∈collectedFamilyTags S := by
          intro entry hm
          rcases hrows.2 entry hm with hm | hm
          · refine ⟨hd.2.2.2 c b tags hA entry.1.1 entry.1.2 hm,?_⟩
            exact List.mem_flatMap.mpr ⟨.mk c b tags,hA,
              collectedDirectTagReachable c b tags entry.1.1 entry.1.2 hm⟩
          · refine ⟨hd.2.2.2 d e rest hB entry.1.1 entry.1.2 hm,?_⟩
            exact List.mem_flatMap.mpr ⟨.mk d e rest,hB,
              collectedDirectTagReachable d e rest entry.1.1 entry.1.2 hm⟩
        have hp : (signedCollectedDifference tags rest).Pairwise
            (fun a b => actualCollectedTagPeak a.1.1 a.1.2 x≠actualCollectedTagPeak b.1.1 b.1.2 x) := by
          apply cell_pairwise_strengthen _ _ _ hrows.1.1
          intro a hma b hmb hkey heq
          have hda := hentry a hma
          have hdb := hentry b hmb
          have he := hpeaks a.1.1 b.1.1 a.1.2 b.1.2 hda.2 hdb.2 heq
          have hab := (collectedFiniteTailSeparation forms hv x hx a.1.2 hda.1 b.1.2 hdb.1).mp he.2
          have hke : collectedTagKey a.1.1 a.1.2=collectedTagKey b.1.1 b.1.2 := by rw [he.1,hab]
          exact (ne_of_lt hkey) hke
        have heq : (actualCollectedPositiveEval (.mk c b tags) x : Int)-
            (actualCollectedPositiveEval (.mk d e rest) x : Int)=
            actualSignedCollectedValue (signedCollectedDifference tags rest) x+
              ((b : Int)-(e : Int))*(x : Int)+((c : Int)-(d : Int)) := by linarith
        have horient := signedCollectedPeakOrientation (signedCollectedDifference tags rest)
          ((b : Int)-(e : Int)) ((c : Int)-(d : Int)) x hrows.1 hn hp (hbudget.1.trans hMx)
        rw [← heq] at horient
        rcases finite_peak_maximum (fun entry : (NONote × CollectedPositiveNF) × Int =>
          actualCollectedTagPeak entry.1.1 entry.1.2 x) (signedCollectedDifference tags rest) hn with
          ⟨entry,hm,hmax⟩
        exact ⟨⟨entry,hm,hmax,horient entry hm hmax⟩,horient⟩

theorem fullActualCollectedCells : Targets.FullActualCollectedCells :=
  ⟨actualOmegaHeadFormula,collectedRangeThresholdCode,collectedNonlinearRangeBand,
    collectedRangeCellTests,actualCollectedSignedCells⟩

end LogicLineages.OrdinalComparison
