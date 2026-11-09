module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerInvariantProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerProof
open PolynomialGraphCompletion WordLinearDecisionCompletion Algorithm Runner

private theorem branch_guard_syntax (D maximum : Nat) (names : List Nat)
    (parent : Work) (b : Branch) (hp : WorkSyntax D maximum names parent)
    (hb : BranchSyntax D maximum (rowVariables parent.row) b) :
    GuardSyntax D maximum names (.conj parent.guard b.guard) := by
  apply conj_guard_syntax D maximum names parent.guard b.guard hp.1
  exact ⟨hb.1,hb.2.1,fun i hi => hp.2.2 i (hb.2.2.1 i hi)⟩

private theorem branch_work_syntax (D maximum : Nat) (names : List Nat)
    (parent : Work) (b : Branch) (w : Work) (hp : WorkSyntax D maximum names parent)
    (hb : BranchSyntax D maximum (rowVariables parent.row) b)
    (he : branchWork parent b = some w) : WorkSyntax D maximum names w := by
  cases ha : b.action with
  | finish o => simp [branchWork,ha] at he
  | descend next =>
      have hw : (⟨next,.conj parent.guard b.guard⟩ : Work) = w := by
        simpa [branchWork,ha] using he
      subst w
      have hnext : RowAllowed D next ∧ NamesFrom (rowVariables parent.row) next := by
        simpa only [ha] using hb.2.2.2
      exact ⟨branch_guard_syntax D maximum names parent b hp hb,hnext.1,
        fun i hi => hp.2.2 i (hnext.2 i hi)⟩

private theorem branch_case_syntax (D maximum : Nat) (names : List Nat)
    (parent : Work) (b : Branch) (c : RowCase) (hp : WorkSyntax D maximum names parent)
    (hb : BranchSyntax D maximum (rowVariables parent.row) b)
    (he : branchFinished parent b = some c) : CaseSyntax D maximum names c := by
  cases ha : b.action with
  | descend next => simp [branchFinished,ha] at he
  | finish o =>
      have hc : (⟨.conj parent.guard b.guard,[o]⟩ : RowCase) = c := by
        simpa [branchFinished,ha] using he
      subst c
      have hout : RowAllowed D o.row ∧ NamesFrom (rowVariables parent.row) o.row ∧
          (o.tag = 0 ∨ o.tag = 2 ∨ (o.tag = 3 ∧ LinearRow maximum o.row)) := by
        simpa only [ha] using hb.2.2.2
      refine ⟨branch_guard_syntax D maximum names parent b hp hb,rfl,?_⟩
      intro out ho
      have heq : out = o := by simpa using ho
      subst out
      exact ⟨hout.1,fun i hi => hp.2.2 i (hout.2.1 i hi),hout.2.2⟩

private theorem branch_work_meaning (maximum : Nat) (source : Row)
    (parent : Work) (b : Branch) (w : Work) (ν : Nat → Nat)
    (hp : WorkMeaning source parent ν) (hd : BranchDomains b ν)
    (hc : BranchCorrect maximum parent.row b ν)
    (he : branchWork parent b = some w) : WorkMeaning source w ν := by
  cases ha : b.action with
  | finish o => simp [branchWork,ha] at he
  | descend next =>
      have hw : (⟨next,.conj parent.guard b.guard⟩ : Work) = w := by
        simpa [branchWork,ha] using he
      subst w
      have hnext : RowDomain next ν := by simpa only [ha] using hd.2
      have hvalue : Formula.eval ν b.guard → RowValue next ν = RowValue parent.row ν := by
        simpa only [BranchCorrect,ha] using hc
      refine ⟨conj_guard_meaningful parent.guard b.guard ν hp.1 hd.1,hnext,?_⟩
      intro hg
      change Formula.eval ν parent.guard ∧ Formula.eval ν b.guard at hg
      exact (hvalue hg.2).trans (hp.2.2 hg.1)

private theorem branch_case_meaning (maximum : Nat) (source : Row)
    (parent : Work) (b : Branch) (c : RowCase) (ν : Nat → Nat)
    (hp : WorkMeaning source parent ν) (hd : BranchDomains b ν)
    (hc : BranchCorrect maximum parent.row b ν)
    (he : branchFinished parent b = some c) : CaseMeaning maximum source c ν := by
  cases ha : b.action with
  | descend next => simp [branchFinished,ha] at he
  | finish o =>
      have heq : (⟨.conj parent.guard b.guard,[o]⟩ : RowCase) = c := by
        simpa [branchFinished,ha] using he
      subst c
      have hout : RowDomain o.row ν := by simpa only [ha] using hd.2
      have hcorrect : Formula.eval ν b.guard → OutcomeCorrect maximum parent.row o ν := by
        simpa only [BranchCorrect,ha] using hc
      refine ⟨conj_guard_meaningful parent.guard b.guard ν hp.1 hd.1,?_,?_⟩
      · intro out ho
        have heq : out = o := by simpa using ho
        subst out
        exact hout
      · intro hg
        change Formula.eval ν parent.guard ∧ Formula.eval ν b.guard at hg
        exact List.Forall₂.cons
          (outcomeCorrect_transfer maximum source parent.row o ν (hp.2.2 hg.1) (hcorrect hg.2))
          List.Forall₂.nil

/-- One actual stack expansion preserves original-name syntax, every emitted
occurrence domain, exact descending row values, and correlated coverage. -/
theorem step_invariant (D maximum : Nat) (hDegree : 3 ≤ D) (source : Row) (s : State)
    (hi : Invariant D maximum source s) : Invariant D maximum source (step D maximum s) := by
  cases hw : s.work with
  | nil => simpa only [step,hw] using hi
  | cons parent rest =>
      have hp : WorkSyntax D maximum (rowVariables source) parent := hi.1 parent (by simp [hw])
      have hsyntax := AlgorithmProof.intrinsicStageSyntaxAndDecrease D maximum parent.row hDegree hp.2.1
      refine ⟨?_,?_,?_⟩
      · intro w hm
        have hmem : w ∈ (stage D maximum parent.row).filterMap (branchWork parent) ∨ w ∈ rest := by
          simpa only [step,hw,List.mem_append] using hm
        rcases hmem with hm | hm
        · obtain ⟨b,hb,he⟩ := List.mem_filterMap.mp hm
          exact branch_work_syntax D maximum (rowVariables source) parent b w hp (hsyntax b hb).1 he
        · exact hi.1 w (by simp [hw,hm])
      · intro c hm
        have hmem : c ∈ (stage D maximum parent.row).filterMap (branchFinished parent) ∨ c ∈ s.finished := by
          simpa only [step,hw,List.mem_append] using hm
        rcases hmem with hm | hm
        · obtain ⟨b,hb,he⟩ := List.mem_filterMap.mp hm
          exact branch_case_syntax D maximum (rowVariables source) parent b c hp (hsyntax b hb).1 he
        · exact hi.2.1 c hm
      · intro ν hregion
        have hr : Region (max s.paid (stageCutoff D maximum parent.row)) maximum (rowVariables source) ν := by
          simpa only [step,hw,stageCutoff] using hregion
        have hold := region_mono s.paid _ maximum (rowVariables source) ν (Nat.le_max_left _ _) hr
        rcases hi.2.2 ν hold with ⟨hsource,hwork,hcases,hcover⟩
        have hparent := hwork parent (by simp [hw])
        have hstage : Region (stageCutoff D maximum parent.row) maximum (rowVariables parent.row) ν := by
          intro i hi
          have hbound := hr i (hp.2.2 i hi)
          exact ⟨(Nat.le_max_right _ _).trans hbound.1,hbound.2⟩
        rcases AlgorithmProof.exactStageSemantics D maximum parent.row hDegree hp.2.1 ν hstage with
          ⟨hparentDomain,hdomains,hbranchcover,hcorrect⟩
        refine ⟨hsource,?_,?_,?_⟩
        · intro w hm
          have hmem : w ∈ (stage D maximum parent.row).filterMap (branchWork parent) ∨ w ∈ rest := by
            simpa only [step,hw,List.mem_append] using hm
          rcases hmem with hm | hm
          · obtain ⟨b,hb,he⟩ := List.mem_filterMap.mp hm
            exact branch_work_meaning maximum source parent b w ν hparent (hdomains b hb) (hcorrect b hb) he
          · exact hwork w (by simp [hw,hm])
        · intro c hm
          have hmem : c ∈ (stage D maximum parent.row).filterMap (branchFinished parent) ∨ c ∈ s.finished := by
            simpa only [step,hw,List.mem_append] using hm
          rcases hmem with hm | hm
          · obtain ⟨b,hb,he⟩ := List.mem_filterMap.mp hm
            exact branch_case_meaning maximum source parent b c ν hparent (hdomains b hb) (hcorrect b hb) he
          · exact hcases c hm
        · rcases hcover with ⟨w,hm,htrue⟩ | ⟨c,hc,htrue⟩
          · have hmem : w = parent ∨ w ∈ rest := by simpa [hw] using hm
            rcases hmem with rfl | hm
            · obtain ⟨b,hb,hbtrue⟩ := hbranchcover
              cases ha : b.action with
              | descend next =>
                  refine Or.inl ⟨⟨next,.conj parent.guard b.guard⟩,?_,?_⟩
                  · have hchild : (⟨next,.conj parent.guard b.guard⟩ : Work) ∈
                        (stage D maximum parent.row).filterMap (branchWork parent) :=
                      List.mem_filterMap.mpr ⟨b,hb,by simp [branchWork,ha]⟩
                    simpa only [step,hw,List.mem_append] using Or.inl hchild
                  · exact ⟨htrue,hbtrue⟩
              | finish o =>
                  refine Or.inr ⟨⟨.conj parent.guard b.guard,[o]⟩,?_,?_⟩
                  · have hchild : (⟨.conj parent.guard b.guard,[o]⟩ : RowCase) ∈
                        (stage D maximum parent.row).filterMap (branchFinished parent) :=
                      List.mem_filterMap.mpr ⟨b,hb,by simp [branchFinished,ha]⟩
                    simpa only [step,hw,List.mem_append] using Or.inl hchild
                  · exact ⟨htrue,hbtrue⟩
            · refine Or.inl ⟨w,?_,htrue⟩
              simpa only [step,hw,List.mem_append] using Or.inr hm
          · refine Or.inr ⟨c,?_,htrue⟩
            simpa only [step,hw,List.mem_append] using Or.inr hc

theorem run_invariant (D maximum : Nat) (hDegree : 3 ≤ D) (source : Row)
    (hsource : RowAllowed D source) (fuel : Nat) :
    Invariant D maximum source (run D maximum source fuel) := by
  induction fuel with
  | zero => exact initial_invariant D maximum source hsource
  | succ fuel ih =>
      simpa only [run,Function.iterate_succ_apply'] using
        step_invariant D maximum hDegree source (run D maximum source fuel) ih

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerProof
