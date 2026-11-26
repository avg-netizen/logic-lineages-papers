module
public import LogicLineages.PermittedControl.OriginalPrintedRankedLiteralHighTargets
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionTransportProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesEnumerateProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesGuardProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesRealizationProof
import LogicLineages.PermittedControl.ActualRankedNormalizationSyntaxRankProof
import LogicLineages.PermittedControl.OriginalPrintedLiteralRowBridgeProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRankedLiteralHigh
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedPlainMatrixInfiniteLow (matrix circuit)
open OriginalPrintedPlainMatrixOrderBranches (branches renamed)
open OriginalPrintedPlainMatrixLinearProjection (top replay updatedTies)
open OriginalMatrixDenseRanks (support renameOperand renameTerm renameRow)
open ActualFiniteOrderBranches (Pattern guard Entry rename realized exactPatternEnumeration exactOrderGuard
  exactBranchRealization)
open OriginalPrintedTerminalBitClauses (BitRow clauses zipBits)
open OriginalRankedLiteralClauseHigh (familyNeed rankedPredecessor OriginalSetup)
open OriginalPrintedLiteralRowBridge (properClauses properClauseMember)
open HeterogeneousSignedMatrixSlice (Row)
open ActualRankedNormalizationSyntax (extend AboveLower exactOriginalSupportRankExtension)

private theorem zipRow (rows : List Row) (bits : List Bool) (r : BitRow) (h : r ∈ zipBits rows bits) :
    r.1 ∈ rows := by
  induction rows generalizing bits with
  | nil => cases bits <;> cases h
  | cons head tail ih =>
    cases bits with
    | nil => cases h
    | cons val vs =>
      rcases List.mem_cons.mp h with same | rest
      · subst r
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih vs rest)

private theorem actualRow (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (positive : Bool) (branch : Pattern) (cs : List BitRow)
    (chosen : cs ∈ rankedFamily known gates p positive branch)
    (row : BitRow) (used : row ∈ cs) :
    row.1 ∈ renamed known gates p branch := by
  let pre := OriginalNormalizedCircuitMatrix.rowsList (circuit known gates p)
  let tail := OriginalPlainTerminalMatrix.rows p
  let ren := renameRow (rename branch)
  obtain ⟨bits,_,rfl⟩ := List.mem_map.mp chosen
  have fromBoth : row.1 ∈ pre.map ren ++ tail.map ren := by
    rcases List.mem_append.mp used with graph | suffix
    · obtain ⟨source,member,rfl⟩ := List.mem_map.mp graph
      exact List.mem_append_left _ member
    · exact List.mem_append_right _ (zipRow _ bits row suffix)
  change row.1 ∈ (pre ++ tail).map ren
  rwa [List.map_append]

private theorem foldBound {α : Type} (f : α → Nat) (xs : List α) (x : α) (h : x ∈ xs) :
    f x ≤ xs.foldr (fun entry n => max (f entry) n) 0 := by
  induction xs with
  | nil => cases h
  | cons s ys ih =>
    rcases List.mem_cons.mp h with same | rest
    · subst s; exact le_max_left _ _
    · exact (ih rest).trans (le_max_right _ _)

private theorem replayOrdered (θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (branch : Pattern) (member : branch ∈ branches known gates p)
    (ordered : (guard branch).eval θ) (z : Nat) (paid : rankedPredecessor (top branch) (realized θ branch) ≤ z) :
    (guard branch).eval (replay θ known gates p branch z) := by
  let names := support (matrix known gates p)
  let baseline := realized θ branch
  let greatest := top branch
  let all := extend baseline greatest z
  obtain ⟨_,keys,bounds,_⟩ := (exactPatternEnumeration names branch).mp member
  obtain ⟨strict,slots,_⟩ := exactBranchRealization θ names branch member ordered
  have above : AboveLower baseline greatest z := by
    intro i lo
    have nz : greatest ≠ 0 := by omega
    have prev : baseline (greatest-1)+1 ≤ z := by
      simpa only [rankedPredecessor,if_neg nz] using paid
    exact (strict.monotone (show i ≤ greatest-1 by omega)).trans_lt (Nat.lt_of_succ_le prev)
  obtain ⟨strong,_,agree⟩ := exactOriginalSupportRankExtension baseline greatest z
    (fun i j h _ => strict h) above
  have actual (e : Entry) (used : e ∈ branch.2) : replay θ known gates p branch z e.1 = all e.2 := by
    have name : e.1 ∈ names := by
      rw [← keys]
      exact List.mem_map.mpr ⟨e,used,rfl⟩
    have current : Function.update baseline greatest z (rename branch e.1) =
        replay θ known gates p branch z e.1 := updatedTies θ known gates p branch member ordered z e.1 name
    rw [(slots e used).1] at current
    have below : e.2 ≤ greatest := by
      have limit := bounds e used
      change e.2 ≤ branch.1-1
      omega
    exact current.symm.trans (agree e.2 below).symm
  apply (exactOrderGuard (replay θ known gates p branch z) branch).mpr
  intro a ha b hb
  rw [actual a ha,actual b hb]
  exact ⟨congrArg all,fun lt => strong lt⟩

theorem exactOriginalChartFunding : ExactOriginalChartFunding := by
  intro B θ known gates p positive funded branch member ordered
  let base := realized θ branch
  let family := rankedFamily known gates p positive branch
  let C := cutoff B known gates p positive
  have across := exactBranchRealization θ (support (matrix known gates p)) branch member ordered
  have allocated : familyNeed B branch.1 family ≤ C :=
    foldBound (fun q => familyNeed B q.1 (rankedFamily known gates p positive q))
      (branches known gates p) branch member
  have info (cs : List BitRow) (c : cs ∈ family) (r : BitRow) (hr : r ∈ cs)
      (t : MixedSameRankResidue.WeightedOperand) (ht : t ∈ r.1.2.2) :
      t.2.rank < branch.1 ∧ t.2.rank ≤ top branch ∧ C ≤ base t.2.rank := by
    have literal := actualRow known gates p positive branch cs c r hr
    obtain ⟨source,atSource,eq⟩ := List.mem_map.mp literal
    rw [← eq] at ht
    obtain ⟨raw,rawHere,h⟩ := List.mem_map.mp ht
    subst t
    have input : raw.2.rank ∈ support (matrix known gates p) :=
      List.mem_flatMap.mpr ⟨source,atSource,List.mem_map.mpr ⟨raw,rawHere,rfl⟩⟩
    obtain ⟨within,read⟩ := across.2.2 raw.2.rank input
    have exactRank : (renameTerm (rename branch) raw).2.rank = rename branch raw.2.rank := by
      rcases raw with ⟨w,op⟩
      cases op <;> rfl
    rw [exactRank]
    refine ⟨within,by change rename branch raw.2.rank ≤ branch.1-1; omega,?_⟩
    change C ≤ realized θ branch (rename branch raw.2.rank)
    rw [read]
    exact funded _ input
  refine ⟨⟨fun _ _ lt _ => across.1 lt,?_,?_⟩,?_⟩
  · intro cs c r hr t ht
    have data := info cs c r hr t ht
    exact ⟨data.1,data.2.1⟩
  · intro cs c r hr t ht _
    exact allocated.trans (info cs ((properClauseMember family cs).mp c).1 r hr t ht).2.2
  · intro z high
    have ceilingPaid : C ≤ z := (le_max_left _ _).trans high
    have prevPaid : rankedPredecessor (top branch) base ≤ z := (le_max_right _ _).trans high
    refine ⟨max_le (allocated.trans ceilingPaid) prevPaid,?_,replayOrdered θ known gates p branch member ordered z prevPaid⟩
    intro name used
    by_cases h : rename branch name = top branch
    · simpa only [replay,if_pos (And.intro used h)] using ceilingPaid
    · have neg : ¬ (name ∈ support (matrix known gates p) ∧ rename branch name = top branch) := fun yes => h yes.2
      simpa only [replay,if_neg neg] using funded name used

end LogicLineages.PermittedControl.OriginalPrintedRankedLiteralHigh
