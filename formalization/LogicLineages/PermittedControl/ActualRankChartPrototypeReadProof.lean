module
public import LogicLineages.PermittedControl.ActualRankChartPrototypeTargets
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesEnumerateProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesGuardProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesRealizationProof
import LogicLineages.PermittedControl.ActualRankedNormalizationSyntaxRankProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRankChartPrototype
open ActualFiniteOrderBranches (Entry Pattern guard rename realized look exactPatternEnumeration
  exactOrderGuard exactBranchRealization)
open ActualRankedNormalizationSyntax (AboveLower extend exactOriginalSupportRankExtension)
open OriginalPrintedPlainMatrixLinearProjection (top)
open OriginalRankedLiteralClauseHigh (rankedPredecessor)

theorem exactChartConsistency : ExactChartConsistency := by
  intro θ branch guarded a ha b hb equal
  have comp := (exactOrderGuard θ branch).mp guarded
  rcases lt_trichotomy a.2 b.2 with small | same | large
  · have bad := (comp a ha b hb).2 small
    rw [equal] at bad
    exact False.elim (lt_irrefl _ bad)
  · exact same
  · have bad := (comp b hb a ha).2 large
    rw [equal] at bad
    exact False.elim (lt_irrefl _ bad)

private theorem named (entries : List Entry) (key rank : Nat)
    (someEntry : ∃ e ∈ entries, e.1 = key)
    (same : ∀ e ∈ entries, e.1 = key → e.2 = rank) :
    look Prod.fst Prod.snd key entries = rank := by
  induction entries with
  | nil => obtain ⟨e,atEntry,_⟩ := someEntry; cases atEntry
  | cons a as ih =>
    by_cases equal : a.1 = key
    · rw [look,if_pos equal]
      exact same a List.mem_cons_self equal
    · rw [look,if_neg equal]
      apply ih
      · obtain ⟨e,used,eq⟩ := someEntry
        rcases List.mem_cons.mp used with first | rest
        · subst e; exact False.elim (equal eq)
        · exact ⟨e,rest,eq⟩
      · exact fun e used eq => same e (List.mem_cons_of_mem _ used) eq

theorem consistentRename (branch : Pattern) (consistent : Consistent branch) (e : Entry) (used : e ∈ branch.2) :
    rename branch e.1 = e.2 :=
  named branch.2 e.1 e.2 ⟨e,used,rfl⟩ (fun d hd eq => consistent d hd e used eq)

theorem exactPrototypeChart : ExactPrototypeChart := by
  intro C names branch member nonempty consistent lower outside lowerChart θ
  let greatest := top branch
  let z := seed C branch lower
  let values := Function.update lower greatest z
  obtain ⟨_,keys,bounds,onto⟩ := (exactPatternEnumeration names branch).mp member
  have isLower (i : Nat) (h : i < greatest) : lower i < z := by
    have nz : greatest ≠ 0 := by omega
    have paid : rankedPredecessor greatest lower ≤ z := le_max_right C _
    rw [rankedPredecessor,if_neg nz] at paid
    have compare : lower i ≤ lower (greatest-1) := by
      have hi : i ≤ greatest-1 := by omega
      rcases lt_or_eq_of_le hi with lt | eq
      · exact (lowerChart.2 i (greatest-1) lt (by omega)).le
      · rw [eq]
    omega
  have extension := exactOriginalSupportRankExtension lower greatest z lowerChart.2 isLower
  have usedName (e : Entry) (h : e ∈ branch.2) : e.1 ∈ names := by
    rw [← keys]
    exact List.mem_map.mpr ⟨e,h,rfl⟩
  have atEntry (e : Entry) (used : e ∈ branch.2) : θ e.1 = values e.2 := by
    change readWithin names branch lower outside z e.1 = values e.2
    rw [readWithin,if_pos (usedName e used),consistentRename branch consistent e used]
  have within (e : Entry) (used : e ∈ branch.2) : e.2 ≤ greatest := by
    have limit := bounds e used
    change e.2 ≤ branch.1-1
    omega
  have guardPaid : (guard branch).eval θ := by
    apply (exactOrderGuard θ branch).mpr
    intro a ha b hb
    rw [atEntry a ha,atEntry b hb]
    constructor
    · exact congrArg values
    · intro ordered
      have lt := extension.1 ordered
      change extend lower greatest z a.2 < extend lower greatest z b.2 at lt
      rw [extension.2.2 a.2 (within a ha),extension.2.2 b.2 (within b hb)] at lt
      exact lt
  have realizedOld := exactBranchRealization θ names branch member guardPaid
  refine ⟨guardPaid,?_,?_⟩
  · intro name used
    rw [← keys] at used
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp used
    rw [atEntry e he]
    rcases lt_or_eq_of_le (within e he) with below | eq
    · change C ≤ Function.update lower greatest z e.2
      rw [Function.update_of_ne (ne_of_lt below)]
      exact lowerChart.1 e.2 below
    · change C ≤ Function.update lower greatest z e.2
      rw [eq,Function.update_self]
      exact le_max_left _ _
  · intro i below
    have withinWidth : i < branch.1 := by
      change i ≤ branch.1-1 at below
      omega
    obtain ⟨e,used,eq⟩ := onto i withinWidth
    rw [← eq,(realizedOld.2.1 e used).2,atEntry e used]

end LogicLineages.PermittedControl.ActualRankChartPrototype
