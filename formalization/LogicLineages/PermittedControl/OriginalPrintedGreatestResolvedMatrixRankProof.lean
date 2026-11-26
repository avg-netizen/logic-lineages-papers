module
public import LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedMatrixTargets
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesRealizationProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedMatrix
open OrdinalComparison FieldComparison
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperand)
open MixedSameRankResidue (WeightedOperand)
open OriginalPrintedGreatestGateResolution (Mode mode plan)
open OriginalPrintedCircuitNormalization (NormalizedGate)
open OriginalNormalizedCircuitMatrix (rows rowsList baseRows limitRows affineRows LimitHead failedRows)
open OriginalFieldGateMatrix (equalityRow zeroRow identityShapeRow identityAffordRow)
open HeterogeneousSignedMatrixSlice (Row)
open OriginalMatrixDenseRanks (support renameRow renameTerm renameOperand)
open OriginalMatrixLinearLowerTable (TopLinear)
open OriginalPrintedPlainMatrixLinearProjection (top)
open OriginalPrintedPlainMatrixInfiniteLow (circuit matrix)
open ActualFiniteOrderBranches (rename exactBranchRealization)
open ActualMixedRowLeadingAnnotations (LinearOperand)

private def badOperand : LowerOperand → List Nat
  | .coordinate _ | .ordinary _ (.iterate 0) => []
  | .ordinary n _ | .count n .. => [n]

private def badTerms (ts : List WeightedOperand) : List Nat := ts.flatMap (fun t => badOperand t.2)
private def badNames (rs : List Row) : List Nat := rs.flatMap (fun r => badTerms r.2.2)

private theorem bareMap {α : Type} (w : α → Int) (n : α → Nat) (xs : List α) :
    badTerms (xs.map (fun x => (w x,.coordinate (n x)))) = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change [] ++ badTerms (xs.map (fun x => (w x,.coordinate (n x)))) = []
      rw [ih] <;> rfl

private theorem affineBad (e : NaturalAffineGateGraph.Expression) (o : Nat) :
    badTerms (AffineCollapseGuardRows.affineTerms e o) = [] := by
  change [] ++ badTerms (e.2.map (fun t => (t.1,.coordinate t.2))) = []
  rw [bareMap Prod.fst Prod.snd] <;> rfl

private theorem originalNames (label : Nat → Nat) (greatest : Nat) (g : NormalizedGate) (n : Nat)
    (h : n ∈ support (emit (mode label greatest g))) : n ∈ support (rows g) := by
  cases g with
  | base base =>
      cases base with
      | affine e o => exact h
      | limitPair head e s o =>
          by_cases atTop : label s = greatest
          · exfalso
            simpa [mode,atTop,emit,failedRows,support] using h
          · simpa [mode,atTop,emit] using h
  | field field =>
      cases field with
      | iterate steps s o =>
          cases steps with
          | zero =>
              simpa [mode,emit,rows,OriginalFieldGateMatrix.rows,equalityRow,support,
                LowerOperand.rank] using h
          | succ k =>
              by_cases atTop : label s = greatest
              · exfalso
                simpa [mode,atTop,emit,failedRows,support] using h
              · simpa [mode,atTop,emit] using h
      | entry interval s o =>
          cases interval with
          | identity mu => exact h
          | proper lam mu =>
              by_cases atTop : label s = greatest
              · exfalso
                simpa [mode,atTop,emit,failedRows,support] using h
              · simpa [mode,atTop,emit] using h
      | count interval s o =>
          cases interval with
          | identity mu => exact h
          | proper lam mu =>
              by_cases atTop : label s = greatest
              · by_cases short : 0 < shortGapLength lam mu
                · have ho : n = s ∨ n = o := by
                    simpa [mode,atTop,short,emit,shortShape,shortValue,identityAffordRow,
                      support,LowerOperand.rank] using h
                  rcases ho with rfl | rfl <;>
                    simp [rows,OriginalFieldGateMatrix.rows,equalityRow,support,LowerOperand.rank]
                · exfalso
                  simpa [mode,atTop,short,emit,failedRows,support] using h
              · simpa only [mode,if_neg atTop,emit] using h

private theorem safeGate (label : Nat → Nat) (greatest : Nat) (g : NormalizedGate) (n : Nat)
    (h : n ∈ badNames (emit (mode label greatest g))) : label n ≠ greatest := by
  cases g with
  | base base =>
      cases base with
      | affine e o =>
          exfalso
          simpa [mode,emit,rows,baseRows,affineRows,badNames,affineBad] using h
      | limitPair head e s o =>
          by_cases atTop : label s = greatest
          · exfalso
            simpa [mode,atTop,emit,failedRows,badNames,badTerms] using h
          · by_cases typed : LimitHead head
            · have actual : n ∈ badNames
                  (AffineCollapseGuardRows.guardRows (OriginalNormalizedCircuitMatrix.typedHead head typed) e s o) := by
                simpa only [mode,if_neg atTop,emit,rows,baseRows,limitRows,dif_pos typed] using h
              change n ∈ badTerms (AffineCollapseGuardRows.affineTerms e s) ++
                (badTerms [(1,.coordinate s)] ++
                  (badTerms (AffineCollapseGuardRows.collapseTerms
                    (OriginalNormalizedCircuitMatrix.typedHead head typed) s o) ++ [])) at actual
              rw [affineBad] at actual
              have eq : n = s := by
                simpa [AffineCollapseGuardRows.collapseTerms,badTerms,badOperand] using actual
              simpa only [eq] using atTop
            · exfalso
              simpa [mode,atTop,emit,rows,baseRows,limitRows,typed,failedRows,badNames,badTerms] using h
  | field field =>
      cases field with
      | iterate steps s o =>
          cases steps with
          | zero =>
              exfalso
              simpa [mode,emit,equalityRow,badNames,badTerms,badOperand] using h
          | succ k =>
              by_cases atTop : label s = greatest
              · exfalso
                simpa [mode,atTop,emit,failedRows,badNames,badTerms] using h
              · have eq : n = s := by
                  simpa [mode,atTop,emit,rows,OriginalFieldGateMatrix.rows,equalityRow,
                    badNames,badTerms,badOperand] using h
                simpa only [eq] using atTop
      | entry interval s o =>
          cases interval with
          | identity mu =>
              exfalso
              simpa [mode,emit,rows,OriginalFieldGateMatrix.rows,identityShapeRow,identityAffordRow,
                equalityRow,badNames,badTerms,badOperand] using h
          | proper lam mu =>
              by_cases atTop : label s = greatest
              · exfalso
                simpa [mode,atTop,emit,failedRows,badNames,badTerms] using h
              · have eq : n = s := by
                  simpa [mode,atTop,emit,rows,OriginalFieldGateMatrix.rows,equalityRow,
                    badNames,badTerms,badOperand] using h
                simpa only [eq] using atTop
      | count interval s o =>
          cases interval with
          | identity mu =>
              exfalso
              simpa [mode,emit,rows,OriginalFieldGateMatrix.rows,identityShapeRow,identityAffordRow,
                zeroRow,badNames,badTerms,badOperand] using h
          | proper lam mu =>
              by_cases atTop : label s = greatest
              · exfalso
                by_cases short : 0 < shortGapLength lam mu <;>
                  simpa [mode,atTop,short,emit,shortShape,shortValue,identityAffordRow,
                    failedRows,badNames,badTerms,badOperand] using h
              · have eq : n = s := by
                  simpa [mode,atTop,emit,rows,OriginalFieldGateMatrix.rows,equalityRow,
                    badNames,badTerms,badOperand] using h
                simpa only [eq] using atTop

private theorem renamedRank (label : Nat → Nat) (op : LowerOperand) :
    (renameOperand label op).rank = label op.rank := by
  cases op <;> rfl

private theorem bareOrBad (label : Nat → Nat) (op : LowerOperand) :
    LinearOperand (renameOperand label op) ∨ op.rank ∈ badOperand op := by
  cases op with
  | coordinate i => exact Or.inl True.intro
  | count i l m => exact Or.inr List.mem_cons_self
  | ordinary i field =>
      cases field with
      | entry a l m => exact Or.inr List.mem_cons_self
      | iterate a =>
          cases a with
          | zero => exact Or.inl True.intro
          | succ a => exact Or.inr List.mem_cons_self

theorem exactResolvedMatrixTopLinear : ExactResolvedMatrixTopLinear := by
  intro θ known gates p branch member ordered
  let tag := rename branch
  let greatest := top branch
  let gs := circuit known gates p
  let pre := prefixRows known gates p branch
  let suffix := OriginalPlainTerminalMatrix.rows p
  let rs := fullRows known gates p branch
  have preOrigin (r : Row) (hr : r ∈ pre) :
      ∃ g ∈ gs, r ∈ emit (mode tag greatest g) := by
    change r ∈ (((gs.map (mode tag greatest)).flatMap emit)) at hr
    obtain ⟨m,hm,here⟩ := List.mem_flatMap.mp hr
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hm
    exact ⟨g,hg,here⟩
  have nameSubset (n : Nat) (hn : n ∈ support rs) : n ∈ support (matrix known gates p) := by
    obtain ⟨r,hr,hname⟩ := List.mem_flatMap.mp hn
    change r ∈ pre ++ suffix at hr
    apply List.mem_flatMap.mpr
    rcases List.mem_append.mp hr with hp | ht
    · obtain ⟨g,hg,there⟩ := preOrigin r hp
      have inGate : n ∈ support (rows g) :=
        originalNames tag greatest g n (List.mem_flatMap.mpr ⟨r,there,hname⟩)
      obtain ⟨r',hr',hname'⟩ := List.mem_flatMap.mp inGate
      have inOriginal : r' ∈ rowsList gs := List.mem_flatMap.mpr ⟨g,hg,hr'⟩
      exact ⟨r',List.mem_append_left _ inOriginal,hname'⟩
    · exact ⟨r,List.mem_append_right _ ht,hname⟩
  have safeBad (n : Nat) (hn : n ∈ badNames rs) : tag n ≠ greatest := by
    obtain ⟨r,hr,bad⟩ := List.mem_flatMap.mp hn
    change r ∈ pre ++ suffix at hr
    rcases List.mem_append.mp hr with hp | ht
    · obtain ⟨g,hg,there⟩ := preOrigin r hp
      exact safeGate tag greatest g n (List.mem_flatMap.mpr ⟨r,there,bad⟩)
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
      change n ∈ badTerms (a.row.2.map (fun t => (t.1,.coordinate t.2.name))) at bad
      have clearNames := bareMap (fun (t : Int × NormalForm.Summand) => t.1)
        (fun (t : Int × NormalForm.Summand) => t.2.name) a.row.2
      rw [clearNames] at bad
      exact False.elim (List.not_mem_nil bad)
  refine ⟨nameSubset,?_⟩
  obtain ⟨_,_,ties⟩ := exactBranchRealization θ (support (matrix known gates p)) branch member ordered
  intro row rowHere t tHere
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp rowHere
  change t ∈ r.2.2.map (renameTerm tag) at tHere
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp tHere
  change (renameOperand tag u.2).rank ≤ greatest ∧
    ((renameOperand tag u.2).rank = greatest → LinearOperand (renameOperand tag u.2))
  rw [renamedRank]
  have nameHere : u.2.rank ∈ support rs :=
    List.mem_flatMap.mpr ⟨r,hr,List.mem_map.mpr ⟨u,hu,rfl⟩⟩
  refine ⟨Nat.le_pred_of_lt (ties _ (nameSubset _ nameHere)).1,?_⟩
  intro atTop
  exact (bareOrBad tag u.2).resolve_right (fun bad =>
    safeBad _ (List.mem_flatMap.mpr ⟨r,hr,List.mem_flatMap.mpr ⟨u,hu,bad⟩⟩) atTop)

end LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedMatrix
