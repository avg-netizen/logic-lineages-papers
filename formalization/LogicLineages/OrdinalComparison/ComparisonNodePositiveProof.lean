module
public import LogicLineages.OrdinalComparison.ComparisonNodePeakOrderProof
public import LogicLineages.OrdinalComparison.CollectedCellsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonNode

attribute [local irreducible] encodedCollectedNormalize encodedPositiveZeroBound encodedCollectedZeroBound

theorem normalized_sign_stable (E F : FixedLimitPositiveExpr)
    (hE : fixedLimitProfileBelow epsilonZero E) (hF : fixedLimitProfileBelow epsilonZero F)
    (leftProfile rightProfile : Nat) (table : ComparisonNodeTable)
    (hcover : comparisonQueryTableCovers (positive_query E F leftProfile rightProfile) table)
    (x y : Nat) (hxT : encodedComparisonTableTail table≤x) (hyT : encodedComparisonTableTail table≤y)
    (hx : encodedPositiveNodeLocalTail (positiveExprEncode E) (positiveExprEncode F)≤x)
    (hy : encodedPositiveNodeLocalTail (positiveExprEncode E) (positiveExprEncode F)≤y) :
    Int.sign ((actualCollectedPositiveEval (collectedPositiveNormalize E) x : Int)-
      (actualCollectedPositiveEval (collectedPositiveNormalize F) x : Int))=
    Int.sign ((actualCollectedPositiveEval (collectedPositiveNormalize E) y : Int)-
      (actualCollectedPositiveEval (collectedPositiveNormalize F) y : Int)) := by
  cases hNE : collectedPositiveNormalize E with
  | mk c b tags =>
    cases hNF : collectedPositiveNormalize F with
    | mk d e rest =>
      have hlocal := source_tail E F hE hF c b d e tags rest hNE hNF
      have hconstX : c+d+1≤x := (Nat.le_max_right _ _).trans (hlocal ▸ hx)
      have hconstY : c+d+1≤y := (Nat.le_max_right _ _).trans (hlocal ▸ hy)
      by_cases hempty : signedCollectedDifference tags rest=[]
      · have heq : tags=rest := (signedCollectedDifferenceEmpty tags rest).mp hempty
        subst rest
        simpa only [actualCollectedPositiveEval,Nat.cast_add,add_sub_add_right_eq_sub] using
          affine_int_sign_stable c b d e x y hconstX hconstY
      · let forms : List CollectedPositiveNF := [.mk c b tags,.mk d e rest]
        have hA : CollectedPositiveValid (.mk c b tags) := by
          rw [←hNE]
          exact collectedPositiveNormalizeValid E hE
        have hB : CollectedPositiveValid (.mk d e rest) := by
          rw [←hNF]
          exact collectedPositiveNormalizeValid F hF
        have hforms : ∀ A∈forms,CollectedPositiveValid A := by
          intro A hA'
          simp only [forms,List.mem_cons,List.not_mem_nil,or_false] at hA'
          rcases hA' with rfl | rfl
          · exact hA
          · exact hB
        have hmemA : CollectedPositiveNF.mk c b tags∈collectedFiniteClosure forms :=
          (collectedFiniteClosureDomain forms hforms).2.1 _ (by simp [forms])
        have hmemB : CollectedPositiveNF.mk d e rest∈collectedFiniteClosure forms :=
          (collectedFiniteClosureDomain forms hforms).2.1 _ (by simp [forms])
        have hcutX : encodedCollectedZeroBound (forms.map collectedPositiveEncode)≤x := by
          rw [encodedCollectedZeroBoundCorrect forms]
          have hz := (Nat.le_max_left _ _).trans (hlocal ▸ hx)
          simpa only [hNE,hNF,forms] using hz
        have hcutY : encodedCollectedZeroBound (forms.map collectedPositiveEncode)≤y := by
          rw [encodedCollectedZeroBoundCorrect forms]
          have hz := (Nat.le_max_left _ _).trans (hlocal ▸ hy)
          simpa only [hNE,hNF,forms] using hz
        have hcellX := (actualCollectedSignedCells.2 forms hforms).2.2 x hcutX _ hmemA _ hmemB
        have hcellY := (actualCollectedSignedCells.2 forms hforms).2.2 y hcutY _ hmemA _ hmemB
        dsimp only [signedCollectedNFRow] at hcellX hcellY
        obtain ⟨entry,he,hmaxY,hsignY⟩ := (hcellY.2 hempty).1
        have hmaxX : ∀ other∈signedCollectedDifference tags rest,
            actualCollectedTagPeak other.1.1 other.1.2 x≤actualCollectedTagPeak entry.1.1 entry.1.2 x := by
          intro other ho
          have ho' : other∈(signedCollectedNFRow (collectedPositiveNormalize E) (collectedPositiveNormalize F)).2.2 := by
            simpa only [hNE,hNF,signedCollectedNFRow] using ho
          have he' : entry∈(signedCollectedNFRow (collectedPositiveNormalize E) (collectedPositiveNormalize F)).2.2 := by
            simpa only [hNE,hNF,signedCollectedNFRow] using he
          exact (row_peak_order_stable E F hE hF leftProfile rightProfile table hcover
            other entry ho' he' x y hxT hyT).mpr (hmaxY other ho)
        exact ((hcellX.2 hempty).2 entry he hmaxX).trans hsignY.symm

theorem positive_correct : Targets.ActualPositiveQueryNodeCorrect := by
  intro E F hE hF leftProfile rightProfile table
  dsimp only
  intro hcover
  let q := positive_query E F leftProfile rightProfile
  let N := max (encodedComparisonTableTail table)
    (encodedPositiveNodeLocalTail (positiveExprEncode E) (positiveExprEncode F))
  have hNE : oneVariableComparisonEncode (.positive E)/2=positiveExprEncode E := by
    change (2*positiveExprEncode E)/2=positiveExprEncode E
    omega
  have hNF : oneVariableComparisonEncode (.positive F)/2=positiveExprEncode F := by
    change (2*positiveExprEncode F)/2=positiveExprEncode F
    omega
  have hresult : encodedPositiveQueryNode q table=
      (encodedSourcePairSignAt (oneVariableComparisonEncode (.positive E)) (oneVariableComparisonEncode (.positive F)) N,N) := by
    simp only [encodedPositiveQueryNode,q,positive_query,hNE,hNF,N]
  rw [hresult]
  have hNT : encodedComparisonTableTail table≤N := Nat.le_max_left _ _
  have hNL : encodedPositiveNodeLocalTail (positiveExprEncode E) (positiveExprEncode F)≤N := Nat.le_max_right _ _
  have hN1 : 1≤N := (table_tail_positive table).trans hNT
  have hpoint := point_program.2.2 (.positive E) (.positive F) hE hF N hN1 hN1
  have hnatN : encodedSourcePairSignAt (oneVariableComparisonEncode (.positive E))
      (oneVariableComparisonEncode (.positive F)) N=
      comparisonNaturalSign (actualFixedLimitProfileEval E N) (actualFixedLimitProfileEval F N) := by
    unfold encodedSourcePairSignAt
    rw [((OneVariableComparison.source_program.2.2 (.positive E) hE).2.2 N hN1).2,
      ((OneVariableComparison.source_program.2.2 (.positive F) hF).2.2 N hN1).2]
    rfl
  have hsign : comparisonEventualSignData (.positive E) (.positive F)
      (encodedSourcePairSignAt (oneVariableComparisonEncode (.positive E)) (oneVariableComparisonEncode (.positive F)) N,N) := by
    refine ⟨hpoint.1,hN1,?_⟩
    intro x hx
    have hi := normalized_sign_stable E F hE hF leftProfile rightProfile table hcover x N
      (hNT.trans hx) hNT (hNL.trans hx) hNL
    rw [collectedPositiveNormalizeValue E hE x,collectedPositiveNormalizeValue F hF x,
      collectedPositiveNormalizeValue E hE N,collectedPositiveNormalizeValue F hF N] at hi
    have hs := sign_of_int_sign _ _ _ _ hi
    refine ⟨True.intro,True.intro,?_⟩
    rw [hnatN,←hs]
    exact (natural_sign (actualFixedLimitProfileEval E x) (actualFixedLimitProfileEval F x)).2
  intro E' F' hEc hFc hEV hFV
  have hEq : E'=.positive E := ComparisonExpansion.source_injective hEc
  have hFq : F'=.positive F := ComparisonExpansion.source_injective hFc
  subst E' F'
  refine ⟨hsign,?_,?_⟩
  · intro _ w eta c A hbad
    cases hbad
  · intro _ w eta c A hbad
    cases hbad

theorem full_positive_node : Targets.FullActualPositiveQueryNode :=
  ⟨point_program,positive_node_program,positive_correct⟩

end LogicLineages.OrdinalComparison.ComparisonNode
