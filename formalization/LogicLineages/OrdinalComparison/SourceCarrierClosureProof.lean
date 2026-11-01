module
public import LogicLineages.OrdinalComparison.SourceCarrierClosureTargets
public import LogicLineages.OrdinalComparison.SourcePeakWordProof
public import LogicLineages.OrdinalComparison.SourceKernelCallsProof
public import LogicLineages.OrdinalComparison.SourceSignatureBudgetProof
public import LogicLineages.OrdinalComparison.SuccessorNormalizationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceCarrierClosure

theorem containment : Targets.DisplayedRawArgumentHeadContainment := by
  intro E
  induction E with
  | constant n => intro p hp; cases hp
  | input => intro p hp; cases hp
  | add E F ihE ihF =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · have h := ihE p hp
      exact ⟨List.mem_append_left _ h.1,fun rho hr => List.mem_append_left _ (h.2 rho hr)⟩
    · have h := ihF p hp
      exact ⟨List.mem_append_right _ h.1,fun rho hr => List.mem_append_right _ (h.2 rho hr)⟩
  | head rho E ih =>
    intro p hp
    by_cases hin : positiveExprHasInput E=true
    · have heq : p=(rho,E) := by simpa only [comparisonDisplayedSourceHeads,hin,if_true,List.mem_singleton] using hp
      subst p
      exact ⟨List.mem_cons_self,fun sigma hs => List.mem_cons_of_mem rho hs⟩
    · have hf : positiveExprHasInput E=false := Bool.eq_false_iff.mpr hin
      simp only [comparisonDisplayedSourceHeads,hf,Bool.false_eq_true,if_false,List.not_mem_nil] at hp

theorem initial : Targets.ActualInitialPairBounds := by
  intro E F hE hF
  dsimp only
  have hDE := SourceSignatureBudget.budget_program.2.2 E hE
  have hDF := SourceSignatureBudget.budget_program.2.2 F hF
  have hEB : comparisonSourceSignatureBudget E≤
      encodedPairSignatureBudget (oneVariableComparisonEncode E) (oneVariableComparisonEncode F) := by
    unfold encodedPairSignatureBudget
    rw [hDE.1,hDF.1]
    exact Nat.le_max_left _ _
  have hFB : comparisonSourceSignatureBudget F≤
      encodedPairSignatureBudget (oneVariableComparisonEncode E) (oneVariableComparisonEncode F) := by
    unfold encodedPairSignatureBudget
    rw [hDE.1,hDF.1]
    exact Nat.le_max_right _ _
  exact ⟨⟨fun rho hr => (hDE.2.2.1 rho hr).trans hEB,fun p hp => (hDE.2.2.2 p hp).trans hEB⟩,
    ⟨fun rho hr => (hDF.2.2.1 rho hr).trans hFB,fun p hp => (hDF.2.2.2 p hp).trans hFB⟩⟩

theorem peak : Targets.ActualPeakChildBounds := by
  intro budget E hE p hp
  have hc := containment E p hp
  have hhead : Vendor.R1.treeWeight p.1.1≤budget := hE.1 p.1 hc.1
  constructor
  · intro rho hr
    have hm : rho∈comparisonPositiveSourceHeads p.2 := by
      simpa only [comparisonSourcePeakWord,comparisonOriginalSourceHeads,comparisonPositiveSourceHeads,List.append_nil] using hr
    exact hE.1 rho (hc.2 rho hm)
  · intro q hq
    have hf := SourcePeakWord.carrier budget p.1 hhead q hq
    exact ((encodedNormalNormBallCorrect budget q.1.1).mp hf.2).2

theorem stripped : Targets.ActualStrippedChildBounds := by
  intro budget w eta c E hE
  constructor
  · intro rho hr
    have hh : comparisonOriginalSourceHeads (comparisonLiteralInner w E)=comparisonPositiveSourceHeads E := by
      cases w <;> rfl
    rw [hh] at hr
    exact hE.1 rho hr
  · intro p hp
    rw [(SourceKernelCalls.shape_semantics.1 w E).2] at hp
    exact hE.2 p (List.mem_append_left _ hp)

theorem normalized : Targets.ActualNormalizedSourceBounds := by
  intro budget w E eta lower c hv hB hPos hLt
  have hEta : Vendor.R1.treeWeight eta.1≤budget :=
    hB.2 (eta,c) (List.mem_append_right _ (List.mem_singleton_self _))
  obtain ⟨added,last,hsource,hcode,hvalid,hlo,hhi,hweight,hstop,hadded,hN,heval⟩ :=
    SuccessorNormalization.actual_program.2 w E eta lower c hv hPos hLt
  refine ⟨added,last,hsource,hB.1,?_⟩
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hp with hp | hp
    · exact hB.2 p (List.mem_append_left _ hp)
    · exact ((hadded p hp).2).trans hEta
  · have heq : p=(last,c) := List.mem_singleton.mp hp
    subst p
    exact hweight.trans hEta

theorem full : Targets.FullActualFixedSourceCarrierClosure := ⟨containment,initial,peak,stripped,normalized⟩

end LogicLineages.OrdinalComparison.SourceCarrierClosure
