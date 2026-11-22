module
public import LogicLineages.PermittedControl.ActualNamedBitFamilyHighTargets
import LogicLineages.PermittedControl.ActualBitFamilyHighRankProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesEnumerateProof
import LogicLineages.PermittedControl.ActualRankChartPrototypeReadProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNamedBitFamilyHigh
open ActualGuardedResidualBitFamily (Family)
open ActualBitFamilyLowSlices (coordinates dimension)
open ActualBitFamilyHigh (ranked renameBit sourceCoordinate)
open ActualFiniteOrderBranches (Pattern rename exactPatternEnumeration)
open ActualRankChartPrototype (seed consistentRename)
open OriginalPrintedPlainMatrixLinearProjection (top)
open OriginalRankedLiteralClauseHigh (familyNeed highMinimum rankedPredecessor)

theorem exactNamedCharts : ExactNamedCharts := by
  intro names p
  simp only [charts,List.mem_filter,decide_eq_true_eq,Valid]

theorem checkedLength (family : Family) (names : List Nat) (h : Supplied family names) :
    names.length = dimension family := by
  have shape : names.toFinset = coordinates family := by
    apply Finset.ext
    intro k
    exact List.mem_toFinset.trans (h.2 k)
  rw [← List.toFinset_card_of_nodup h.1,shape]

theorem renameIndex (names : List Nat) (p : Pattern) (good : Valid names p)
    (k : Nat) (used : k ∈ names) : rename p k < p.1 := by
  obtain ⟨_,keys,bound,_⟩ := (exactPatternEnumeration names p).mp good.1
  rw [← keys] at used
  obtain ⟨e,member,rfl⟩ := List.mem_map.mp used
  rw [consistentRename p good.2.2 e member]
  exact bound e member

private theorem scopeNamed (family : Family) (names : List Nat) (p : Pattern)
    (support : Supplied family names) (good : Valid names p) :
    ∀ clause ∈ ranked p family, ∀ r ∈ clause, ∀ t ∈ r.1.2.2, t.2.rank < p.1 := by
  intro clause used r inRow t inTerm
  obtain ⟨source,atSource,rfl⟩ := List.mem_map.mp used
  obtain ⟨row,atRow,rfl⟩ := List.mem_map.mp inRow
  obtain ⟨raw,atRaw,rfl⟩ := List.mem_map.mp inTerm
  have bound := renameIndex names p good raw.2.rank
    ((support.2 _).mpr (sourceCoordinate family source atSource row atRow raw atRaw))
  rcases raw with ⟨w,op⟩
  cases op <;> exact bound

private theorem foldMaximum {α : Type} (cost : α → Nat) (xs : List α) (x : α) (h : x ∈ xs) :
    cost x ≤ xs.foldr (fun a n => max (cost a) n) 0 := by
  induction xs with
  | nil => cases h
  | cons a xs ih =>
    rcases List.mem_cons.mp h with same | rest
    · subst a
      exact le_max_left _ _
    · exact (ih rest).trans (le_max_right _ _)

private theorem cutoffPays (B : Nat) (family : Family) (names : List Nat) (p : Pattern)
    (good : Valid names p) : familyNeed B p.1 (ranked p family) ≤ cutoff B family names := by
  let cost : Pattern → Nat := fun p => familyNeed B p.1 (ranked p family)
  change cost p ≤ (charts names).foldr (fun a n => max (cost a) n) 0
  exact foldMaximum cost (charts names) p ((exactNamedCharts names p).mpr good)

theorem exactNamedHighSetup : ExactNamedHighSetup := by
  intro B family names p supports valid lower chart
  have static := cutoffPays B family names p valid
  have sourceScope := scopeNamed family names p supports valid
  refine ⟨⟨chart.2,?_,?_⟩,?_⟩
  · intro c hc row hr t ht
    have h := sourceScope c hc row hr t ht
    exact ⟨h,by change t.2.rank ≤ p.1-1; omega⟩
  · intro c hc r hr t ht below
    exact static.trans (chart.1 t.2.rank below)
  · intro z high
    change max (familyNeed B p.1 (ranked p family)) (rankedPredecessor (top p) lower) ≤ z
    exact max_le (static.trans ((le_max_left _ _).trans high)) ((le_max_right _ _).trans high)

end LogicLineages.PermittedControl.ActualNamedBitFamilyHigh
