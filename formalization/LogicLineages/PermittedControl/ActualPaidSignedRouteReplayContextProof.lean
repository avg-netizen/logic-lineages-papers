module
public import LogicLineages.PermittedControl.ActualPaidSignedRouteReplayTargets
import LogicLineages.PermittedControl.ActualPaidOrderedSyntaxReadsProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualPaidSignedRouteReplay
open OrdinalComparison PreparedProjection
open ActualFiniteGlobalTail (globalTail syntaxOf)
open ActualGlobalComparisonCeiling (comparisonCeiling)
open ActualReadChargeIteration (ReadState)
open ActualRankedNormalizationSyntax (AboveLower)
open ActualSymbolicZeroSuccessor (SyntaxState)
open ActualPaidOrderedSyntaxReads (readCeiling PaidReadCeiling exactPaidOrderedSyntaxReads)
open ActualBoundedSignedRouteSemantics (RunContext stateSyntax)
open ActualTraceSignCutoff (terminalCutoffCeiling constantCeiling stepCeiling massCeiling)
open ActualSignedReadMass (signedMass)
open MixedSameRankResidue (WeightedOperand)

private theorem dummySyntax (s : SyntaxState) : syntaxOf (dummy s) = s.terms := by
  simp [syntaxOf,dummy,List.map_map,Function.comp_def]

private theorem dummyMass (rs : List ActualZeroClassReplacement.Read) :
    signedMass ((rs.map Prod.fst).map fun t => (t,0)) = signedMass rs := by
  simp only [signedMass,List.map_map,Function.comp_def]

theorem exactSignCutoffFromSyntax : ExactSignCutoffFromSyntax := by
  intro r s
  have sameSyntax : syntaxOf (dummy (stateSyntax s)) = syntaxOf s := dummySyntax (stateSyntax s)
  have sameMass : signedMass (dummy (stateSyntax s)).reads = signedMass s.reads := dummyMass s.reads
  have sameConstant : (dummy (stateSyntax s)).constant = s.constant := rfl
  simp only [terminalCutoffCeiling,constantCeiling,stepCeiling,massCeiling,sameSyntax,sameMass,sameConstant]

private theorem above {B r top : Nat} {baseline : Nat → Nat} {s : SyntaxState}
    (setup : LowerSetup B r top baseline s) {z : Nat}
    (minimum : replayMinimum B r top baseline s ≤ z) : AboveLower baseline top z := by
  intro i below
  have htop : top ≠ 0 := by omega
  have previous : (if top = 0 then 0 else baseline (top-1)+1) = baseline (top-1)+1 := if_neg htop
  have bound : baseline (top-1) + 1 ≤ z := by
    rw [← previous]
    exact (le_max_right _ _).trans ((le_max_right _ _).trans minimum)
  have cmp : i ≤ top-1 := by omega
  rcases lt_or_eq_of_le cmp with lt | eq
  · have head : top-1 < top := by omega
    exact (setup.strict i (top-1) lt head).trans (by omega)
  · simpa only [eq] using (show baseline (top-1) < z by omega)

theorem exactActualReplayContext : ExactActualReplayContext := by
  intro f B selected r top baseline s setup z minimum
  let θ := Function.update baseline top z
  have commonAt (t : WeightedOperand) (used : t ∈ s.terms) :
      commonMinimum B r s ≤ θ t.2.rank := by
    rcases lt_or_eq_of_le (setup.scope t used).2 with smaller | same
    · have ne : t.2.rank ≠ top := ne_of_lt smaller
      change commonMinimum B r s ≤ Function.update baseline top z t.2.rank
      rw [Function.update_of_ne ne]
      exact setup.paid t used smaller
    · change commonMinimum B r s ≤ Function.update baseline top z t.2.rank
      rw [same,Function.update_self]
      exact (le_max_left _ _).trans minimum
  have readPaid : PaidReadCeiling θ s.terms :=
    fun t used => (le_max_left _ _).trans (commonAt t used)
  refine ⟨exactPaidOrderedSyntaxReads f B selected θ s setup.proper readPaid,?_⟩
  intro original frames live
  have terms : syntaxOf original = s.terms := congrArg SyntaxState.terms frames
  have owns (rd : ActualZeroClassReplacement.Read) (used : rd ∈ original.reads) :
      rd.1 ∈ s.terms := by
    rw [← terms]
    exact List.mem_map.mpr ⟨rd,used,rfl⟩
  refine ⟨selected,setup.strict,above setup minimum,live,
    fun rd used => setup.scope rd.1 (owns rd used),
    fun rd used => setup.long rd.1 (owns rd used),?_,?_,?_⟩
  · change ∀ t ∈ syntaxOf original, globalTail B r (syntaxOf original) ≤ θ t.2.rank
    rw [terms]
    intro t used
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (commonAt t used))
  · change ∀ t ∈ syntaxOf original, comparisonCeiling B r (syntaxOf original) ≤ θ t.2.rank
    rw [terms]
    intro t used
    exact (le_max_right _ _).trans ((le_max_right _ _).trans (commonAt t used))
  · rw [exactSignCutoffFromSyntax r original,frames]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans minimum)

end LogicLineages.PermittedControl.ActualPaidSignedRouteReplay
