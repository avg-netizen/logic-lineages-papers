module
public import LogicLineages.StandardControlCurrent.HFreeGraphNormalizationTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationCodeCalibrationProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.HFreeGraphNormalizationProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion NonlinearProjectionCompletion
open HFreeGraphNormalization
open HFreeGraphNormalization.Code

 theorem termVariables_step (n tag : Nat) (ht : tag < 10) :
    Code.termVariables (10 * n + tag) =
      if tag = 0 then []
  else if tag = 1 then [n]
  else if tag = 2 ∨ tag = 3 then
    termVariables (n).unpair.1 ++ termVariables (n).unpair.2
  else if tag = 4 ∨ tag = 5 then termVariables (n).unpair.2
  else termVariables (n) := by
  have hm : (10 * n + tag) % 10 = tag := by omega
  have hd : (10 * n + tag) / 10 = n := by omega
  rw [Code.termVariables,hm,hd]

 theorem matrixVariables_step (n tag : Nat) (ht : tag < 8) :
    Code.matrixVariables (8 * n + tag) =
      if tag = 0 ∨ tag = 1 then []
  else if tag = 2 ∨ tag = 3 then
    termVariables (n).unpair.1 ++ termVariables (n).unpair.2
  else if tag = 4 then termVariables (n).unpair.2
  else if tag = 5 then matrixVariables (n)
  else matrixVariables (n).unpair.1 ++ matrixVariables (n).unpair.2 := by
  have hm : (8 * n + tag) % 8 = tag := by omega
  have hd : (8 * n + tag) / 8 = n := by omega
  rw [Code.matrixVariables,hm,hd]

 theorem forest_step (n tag : Nat) (ht : tag < 8) :
    Code.forest (8 * n + tag) =
      if tag = 0 ∨ tag = 1 then 0
  else if tag = 2 ∨ tag = 3 then 10 * (n) + 2
  else if tag = 4 then (n).unpair.2
  else if tag = 5 then forest (n)
  else 10 * Nat.pair (forest (n).unpair.1) (forest (n).unpair.2) + 2 := by
  have hm : (8 * n + tag) % 8 = tag := by omega
  have hd : (8 * n + tag) / 8 = n := by omega
  rw [Code.forest,hm,hd]

 theorem predicate_step (start : Nat) (n tag : Nat) (ht : tag < 8) :
    Code.predicate start (8 * n + tag) =
      if tag = 0 then 0
  else if tag = 1 then 1
  else if tag = 2 ∨ tag = 3 then
    let a := (n).unpair.1
    let b := (n).unpair.2
    SourceRows.Code.relation (decide (tag = 3)) (ExpandedGraphCode.output start a)
      (ExpandedGraphCode.output (start + ExpandedGraphCode.nodeCount a) b)
  else if tag = 4 then
    let m := (n).unpair.1
    let z := ExpandedGraphCode.output start (n).unpair.2
    let row : NormalForm.Code.RowData := (0,[(1,SourceTermGraph.Code.variableData z)])
    if m = 0 then SourceTermGraph.Code.equation row
    else 6 * Encodable.encode ((1,m-1,row) : NormalForm.Code.AtomData) + 2
  else if tag = 5 then 6 * predicate start (n) + 3
  else 6 * Nat.pair (predicate start (n).unpair.1)
    (predicate (start + ExpandedGraphCode.nodeCount (forest (n).unpair.1))
      (n).unpair.2) + (tag - 2) := by
  have hm : (8 * n + tag) % 8 = tag := by omega
  have hd : (8 * n + tag) / 8 = n := by omega
  rw [Code.predicate,hm,hd]

theorem termVariables_calibration (t : Term) : Code.termVariables t.encode = t.variables := by
  induction t with
  | numeral n =>
      simpa only [Term.encode,Term.variables,Nat.add_zero,Nat.reduceEqDiff,
        ↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or] using
        termVariables_step (n) 0 (by decide)
  | «variable» i =>
      simpa only [Term.encode,Term.variables,Nat.add_zero,Nat.reduceEqDiff,
        ↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or] using
        termVariables_step (i) 1 (by decide)
  | add a b ha hb =>
      simpa only [Term.encode,Term.variables,Nat.add_zero,Nat.reduceEqDiff,
        ↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or, ha, hb] using
        termVariables_step (Nat.pair a.encode b.encode) 2 (by decide)
  | subtract a b ha hb =>
      simpa only [Term.encode,Term.variables,Nat.add_zero,Nat.reduceEqDiff,
        ↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or, ha, hb] using
        termVariables_step (Nat.pair a.encode b.encode) 3 (by decide)
  | multiply c a ha =>
      simpa only [Term.encode,Term.variables,Nat.add_zero,Nat.reduceEqDiff,
        ↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or, ha] using
        termVariables_step (Nat.pair c a.encode) 4 (by decide)
  | divide c a ha =>
      simpa only [Term.encode,Term.variables,Nat.add_zero,Nat.reduceEqDiff,
        ↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or, ha] using
        termVariables_step (Nat.pair c a.encode) 5 (by decide)
  | phi a ha =>
      simpa only [Term.encode,Term.variables,Nat.add_zero,Nat.reduceEqDiff,
        ↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or, ha] using
        termVariables_step (a.encode) 6 (by decide)
  | hyper a ha =>
      simpa only [Term.encode,Term.variables,Nat.add_zero,Nat.reduceEqDiff,
        ↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or, ha] using
        termVariables_step (a.encode) 7 (by decide)
  | phiInverse a ha =>
      simpa only [Term.encode,Term.variables,Nat.add_zero,Nat.reduceEqDiff,
        ↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or, ha] using
        termVariables_step (a.encode) 8 (by decide)
  | hyperInverse a ha =>
      simpa only [Term.encode,Term.variables,Nat.add_zero,Nat.reduceEqDiff,
        ↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or, ha] using
        termVariables_step (a.encode) 9 (by decide)

theorem matrixVariables_calibration (p : Matrix) : Code.matrixVariables p.encode = p.variables := by
  induction p with
  | truth =>
      simpa only [Matrix.encode,Matrix.variables,Nat.add_zero,Nat.zero_mul,Nat.zero_add,
        Nat.reduceEqDiff,↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or,
        termVariables_calibration] using matrixVariables_step (0) 0 (by decide)
  | falsity =>
      simpa only [Matrix.encode,Matrix.variables,Nat.add_zero,Nat.zero_mul,Nat.zero_add,
        Nat.reduceEqDiff,↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or,
        termVariables_calibration] using matrixVariables_step (0) 1 (by decide)
  | equal a b =>
      simpa only [Matrix.encode,Matrix.variables,Nat.add_zero,Nat.zero_mul,Nat.zero_add,
        Nat.reduceEqDiff,↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or,
        termVariables_calibration] using matrixVariables_step (Nat.pair a.encode b.encode) 2 (by decide)
  | less a b =>
      simpa only [Matrix.encode,Matrix.variables,Nat.add_zero,Nat.zero_mul,Nat.zero_add,
        Nat.reduceEqDiff,↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or,
        termVariables_calibration] using matrixVariables_step (Nat.pair a.encode b.encode) 3 (by decide)
  | divisible m a =>
      simpa only [Matrix.encode,Matrix.variables,Nat.add_zero,Nat.zero_mul,Nat.zero_add,
        Nat.reduceEqDiff,↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or,
        termVariables_calibration] using matrixVariables_step (Nat.pair m a.encode) 4 (by decide)
  | negative p hp =>
      simpa only [Matrix.encode,Matrix.variables,Nat.add_zero,Nat.zero_mul,Nat.zero_add,
        Nat.reduceEqDiff,↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or,
        termVariables_calibration, hp] using matrixVariables_step (p.encode) 5 (by decide)
  | conjunction p q hp hq =>
      simpa only [Matrix.encode,Matrix.variables,Nat.add_zero,Nat.zero_mul,Nat.zero_add,
        Nat.reduceEqDiff,↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or,
        termVariables_calibration, hp, hq] using matrixVariables_step (Nat.pair p.encode q.encode) 6 (by decide)
  | disjunction p q hp hq =>
      simpa only [Matrix.encode,Matrix.variables,Nat.add_zero,Nat.zero_mul,Nat.zero_add,
        Nat.reduceEqDiff,↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or,
        termVariables_calibration, hp, hq] using matrixVariables_step (Nat.pair p.encode q.encode) 7 (by decide)

theorem forest_calibration (p : Matrix) : Code.forest p.encode = (ExpandedBooleanGraph.forest p).encode := by
  induction p with
  | truth =>
      simpa only [Matrix.encode,ExpandedBooleanGraph.forest,Term.encode,Nat.add_zero,Nat.zero_mul,Nat.zero_add,
        Nat.reduceEqDiff,↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or] using
        forest_step (0) 0 (by decide)
  | falsity =>
      simpa only [Matrix.encode,ExpandedBooleanGraph.forest,Term.encode,Nat.add_zero,Nat.zero_mul,Nat.zero_add,
        Nat.reduceEqDiff,↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or] using
        forest_step (0) 1 (by decide)
  | equal a b =>
      simpa only [Matrix.encode,ExpandedBooleanGraph.forest,Term.encode,Nat.add_zero,Nat.zero_mul,Nat.zero_add,
        Nat.reduceEqDiff,↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or] using
        forest_step (Nat.pair a.encode b.encode) 2 (by decide)
  | less a b =>
      simpa only [Matrix.encode,ExpandedBooleanGraph.forest,Term.encode,Nat.add_zero,Nat.zero_mul,Nat.zero_add,
        Nat.reduceEqDiff,↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or] using
        forest_step (Nat.pair a.encode b.encode) 3 (by decide)
  | divisible m a =>
      simpa only [Matrix.encode,ExpandedBooleanGraph.forest,Term.encode,Nat.add_zero,Nat.zero_mul,Nat.zero_add,
        Nat.reduceEqDiff,↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or] using
        forest_step (Nat.pair m a.encode) 4 (by decide)
  | negative p hp =>
      simpa only [Matrix.encode,ExpandedBooleanGraph.forest,Term.encode,Nat.add_zero,Nat.zero_mul,Nat.zero_add,
        Nat.reduceEqDiff,↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or, hp] using
        forest_step (p.encode) 5 (by decide)
  | conjunction p q hp hq =>
      simpa only [Matrix.encode,ExpandedBooleanGraph.forest,Term.encode,Nat.add_zero,Nat.zero_mul,Nat.zero_add,
        Nat.reduceEqDiff,↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or, hp, hq] using
        forest_step (Nat.pair p.encode q.encode) 6 (by decide)
  | disjunction p q hp hq =>
      simpa only [Matrix.encode,ExpandedBooleanGraph.forest,Term.encode,Nat.add_zero,Nat.zero_mul,Nat.zero_add,
        Nat.reduceEqDiff,↓reduceIte,Nat.unpair_pair,or_true,true_or,or_false,false_or, hp, hq] using
        forest_step (Nat.pair p.encode q.encode) 7 (by decide)

end LogicLineages.StandardControlCurrent.HFreeGraphNormalizationProof
