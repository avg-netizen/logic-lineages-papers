module
public import LogicLineages.OrdinalComparison.CollectedFiniteTailTargets
public import LogicLineages.OrdinalComparison.CollectedOneInputProof
public import LogicLineages.OrdinalComparison.CollectedFiniteClosureProof
public import LogicLineages.OrdinalComparison.SignedCollectedBudgetProof
public import LogicLineages.OrdinalComparison.SparseSignedCollectedProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem threshold_fold_le (forms : List CollectedPositiveNF) (N : Nat) (hN : 1≤N)
    (h : ∀ A∈forms, collectedOneInputThreshold A≤N) : collectedFamilyThreshold forms≤N := by
  induction forms with
  | nil => exact hN
  | cons A forms ih =>
    exact max_le (h A List.mem_cons_self) (ih (fun B hB => h B (List.mem_cons_of_mem A hB)))

private theorem family_threshold_positive (forms : List CollectedPositiveNF) : 1≤collectedFamilyThreshold forms := by
  induction forms with
  | nil => exact le_rfl
  | cons A forms ih => exact ih.trans (le_max_right _ _)

private theorem pairwise_strengthen {α : Type} (l : List α) (R S : α → α → Prop)
    (hp : l.Pairwise R) (h : ∀ a∈l, ∀ b∈l, R a b → S a b) : l.Pairwise S := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    have hd := List.pairwise_cons.mp hp
    exact List.pairwise_cons.mpr
      ⟨fun b hb => h a List.mem_cons_self b (List.mem_cons_of_mem a hb) (hd.1 b hb),
        ih hd.2 (fun b hb c hc hr => h b (List.mem_cons_of_mem a hb) c (List.mem_cons_of_mem a hc) hr)⟩

theorem collectedFiniteTailSeparation : Targets.CollectedFiniteTailSeparation := by
  intro forms hv x hx
  let S := collectedFiniteClosure forms
  have hd := collectedFiniteClosureDomain forms hv
  have hvalid : ∀ A∈S, CollectedPositiveValid A := hd.2.2.1
  have hthreshold : collectedFamilyThreshold S≤collectedFamilyThreshold forms :=
    threshold_fold_le S _ (family_threshold_positive forms)
      (fun A hA => (collectedClosureBounds forms A hA).2)
  have hsource := fullActualCollectedOneInput.2 S hvalid
  have hSx : encodedCollectedFamilyThreshold (S.map collectedPositiveEncode)≤x := by
    rw [encodedCollectedFamilyThresholdCorrect S]
    exact hthreshold.trans ((le_max_left _ _).trans hx)
  have hpeaks := (hsource.2.2 x hSx).2
  have hMx : max 4 (8*collectedRootCodeBound forms+1)≤x := (le_max_right _ _).trans hx
  have hsep : ∀ h : Nat, ∀ A∈S, ∀ B∈S,
      collectedPositiveHeight A≤h → collectedPositiveHeight B≤h →
      actualCollectedPositiveEval A x=actualCollectedPositiveEval B x → A=B := by
    intro h
    induction h using Nat.strong_induction_on with
    | h h ih =>
      intro A hA B hB ha hb heval
      cases A with
      | mk c b tags =>
        cases B with
        | mk d e rest =>
          have hvA : CollectedTagsValid tags := hvalid _ hA
          have hvB : CollectedTagsValid rest := hvalid _ hB
          have hrows := signedCollectedDifferenceValid tags rest hvA hvB
          have hbudget := signedCollectedPairBudget (.mk c b tags) (.mk d e rest)
            (collectedRootCodeBound forms)
            (collectedClosureBounds forms _ hA).1 (collectedClosureBounds forms _ hB).1
          dsimp only [signedCollectedNFRow] at hbudget
          have hroweq := signedCollectedNFRowValue (.mk c b tags) (.mk d e rest) x
          dsimp only [signedCollectedNFRow] at hroweq
          rw [heval,sub_self] at hroweq
          have hzero : actualSignedCollectedValue (signedCollectedDifference tags rest) x+
              ((b : Int)-(e : Int))*(x : Int)+((c : Int)-(d : Int))=0 := by linarith
          by_cases hempty : signedCollectedDifference tags rest=[]
          · have hval : actualSignedCollectedValue (signedCollectedDifference tags rest) x=0 := by
              rw [hempty]
              rfl
            rw [hval,zero_add] at hzero
            have hp : (b : Int)-(e : Int)=0 := by
              by_contra hp
              exact signedAffineTailNonzero _ _ x hp (hbudget.2.trans hMx) hzero
            have hq : (c : Int)-(d : Int)=0 := by
              simpa only [hp,zero_mul,zero_add] using hzero
            exact (signedCollectedRowIdentity (.mk c b tags) (.mk d e rest)).mp ⟨hq,hp,hempty⟩
          · have hentry : ∀ entry∈signedCollectedDifference tags rest,
                entry.1.2∈S ∧ collectedPositiveHeight entry.1.2<h ∧ entry.1∈collectedFamilyTags S := by
              intro entry hm
              rcases hrows.2 entry hm with hm | hm
              · refine ⟨hd.2.2.2 c b tags hA entry.1.1 entry.1.2 hm,
                  (collectedDirectChildHeight c b tags entry.1.1 entry.1.2 hm).trans_le ha,?_⟩
                exact List.mem_flatMap.mpr ⟨.mk c b tags,hA,
                  collectedDirectTagReachable c b tags entry.1.1 entry.1.2 hm⟩
              · refine ⟨hd.2.2.2 d e rest hB entry.1.1 entry.1.2 hm,
                  (collectedDirectChildHeight d e rest entry.1.1 entry.1.2 hm).trans_le hb,?_⟩
                exact List.mem_flatMap.mpr ⟨.mk d e rest,hB,
                  collectedDirectTagReachable d e rest entry.1.1 entry.1.2 hm⟩
            have hp : (signedCollectedDifference tags rest).Pairwise
                (fun a b => actualCollectedTagPeak a.1.1 a.1.2 x≠actualCollectedTagPeak b.1.1 b.1.2 x) := by
              apply pairwise_strengthen _ _ _ hrows.1.1
              intro a hma b hmb hkey heq
              have hda := hentry a hma
              have hdb := hentry b hmb
              have he := hpeaks a.1.1 b.1.1 a.1.2 b.1.2 hda.2.2 hdb.2.2 heq
              have hab : a.1.2=b.1.2 :=
                ih (max (collectedPositiveHeight a.1.2) (collectedPositiveHeight b.1.2))
                  (max_lt_iff.mpr ⟨hda.2.1,hdb.2.1⟩) a.1.2 hda.1 b.1.2 hdb.1
                  (le_max_left _ _) (le_max_right _ _) he.2
              have hke : collectedTagKey a.1.1 a.1.2=collectedTagKey b.1.1 b.1.2 := by rw [he.1,hab]
              exact (ne_of_lt hkey) hke
            exact False.elim (sparseSignedCollectedNonzero (signedCollectedDifference tags rest)
              ((b : Int)-(e : Int)) ((c : Int)-(d : Int)) x hrows.1 hempty hp
              (hbudget.1.trans hMx) hzero)
  intro A hA B hB
  constructor
  · exact hsep (max (collectedPositiveHeight A) (collectedPositiveHeight B)) A hA B hB
      (le_max_left _ _) (le_max_right _ _)
  · intro h; rw [h]

end LogicLineages.OrdinalComparison
