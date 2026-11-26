module
public import LogicLineages.StandardControlCurrent.OrderedOccurrenceRawDefinitions
public import Mathlib.Data.List.Enum
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormCodeCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindowCodeProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.OrderedOccurrenceRaw
open OrdinalComparison LayeredComparison.SnyatkovCompletion NormalForm

def occurrenceData (o : OrderedOccurrence.Occurrence) : RawOccurrence :=
  (o.1,o.2.1,o.2.2.1,o.2.2.2.data)

private theorem rows_step (n tag : Nat) (ht : tag<6) :
    rows (6*n+tag) = if tag<2 then []
    else if tag=2 then [((Encodable.decode n : Option Code.AtomData).getD (0,0,0,[])).2.2]
    else if tag=3 then rows n else rows n.unpair.1 ++ rows n.unpair.2 := by
  have hm : (6*n+tag)%6=tag := by omega
  have hd : (6*n+tag)/6=n := by omega
  rw [rows,hm,hd]

theorem rows_calibration (p : Formula) : rows p.encode=(OrderedOccurrence.rows p).map rowData := by
  induction p with
  | truth => simpa [Formula.encode,OrderedOccurrence.rows] using rows_step 0 0 (by decide)
  | falsity => simpa [Formula.encode,OrderedOccurrence.rows] using rows_step 0 1 (by decide)
  | atom a =>
    have h := rows_step (Encodable.encode a.data) 2 (by decide)
    simp only [show ¬(2<2) by decide,if_false,if_true,Encodable.encodek,Option.getD_some] at h
    cases a <;> simpa [Formula.encode,OrderedOccurrence.rows,Atom.data,Atom.row] using h
  | negative p ih => simpa [Formula.encode,OrderedOccurrence.rows,ih] using rows_step p.encode 3 (by decide)
  | conjunction p q ihp ihq =>
    simpa [Formula.encode,OrderedOccurrence.rows,Nat.unpair_pair,ihp,ihq] using rows_step (Nat.pair p.encode q.encode) 4 (by decide)
  | disjunction p q ihp ihq =>
    simpa [Formula.encode,OrderedOccurrence.rows,Nat.unpair_pair,ihp,ihq] using rows_step (Nat.pair p.encode q.encode) 5 (by decide)

theorem roster_calibration (p : Formula) : roster p.encode=(OrderedOccurrence.roster p).map occurrenceData := by
  simp [roster,OrderedOccurrence.roster,rows_calibration,List.zipIdx_map,List.flatMap_map,
    List.map_flatMap,List.map_map,rowData,occurrenceData,Function.comp_def]

theorem name_calibration (o : OrderedOccurrence.Occurrence) : name (occurrenceData o)=(OrderedOccurrence.summand o).name := by
  rcases o with ⟨r,j,c,s⟩
  cases s <;> rfl

theorem term_calibration (o : OrderedOccurrence.Occurrence) : term (occurrenceData o)=(OrderedOccurrence.summand o).term.encode :=
  NormalFormCodeProof.item_term _

private theorem live_test (xs : List Nat) (o : OrderedOccurrence.Occurrence) :
    ((occurrenceData o).2.2.1 != 0 && (occurrenceData o).2.2.2.1 != 0 && name (occurrenceData o) ∈ xs) =
    (OrderedOccurrence.coefficient o != 0 && OrderedOccurrence.nonlinear (OrderedOccurrence.summand o) && (OrderedOccurrence.summand o).name ∈ xs) := by
  rcases o with ⟨r,j,c,s⟩
  cases s <;> simp [occurrenceData,name,OrderedOccurrence.coefficient,OrderedOccurrence.summand,
    OrderedOccurrence.nonlinear,Summand.data,Summand.name] <;> rfl

theorem live_calibration (xs : List Nat) (p : Formula) :
    live xs p.encode=(OrderedOccurrence.live xs p).map occurrenceData := by
  simp only [live,roster_calibration,List.filter_map,Function.comp_def,live_test,
    OrderedOccurrence.live]

theorem inactive_calibration (xs : List Nat) (p : Formula) : inactive xs p.encode=OrderedOccurrence.inactive xs p := by
  simp [inactive,OrderedOccurrence.inactive,live_calibration,List.any_map,Function.comp_def,name_calibration]

theorem all_calibration (ps : List Matrix) : all (ps.map Matrix.encode)=(OrderedOccurrence.all ps).encode := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simpa [all,OrderedOccurrence.all,Matrix.encode,WindowCode.conjunction] using congrArg (WindowCode.conjunction p.encode) ih

theorem strict_calibration (xs : List Nat) : strictOrder xs=(OrderedOccurrence.strictOrder xs).encode := by
  rw [OrderedOccurrence.strictOrder,← all_calibration]
  simp [strictOrder,List.map_flatMap,List.map_map,Function.comp_def,Matrix.encode,Term.encode,WindowCode.less,WindowCode.var]

theorem maximal_calibration (xs : List Nat) (p : Formula) (o : OrderedOccurrence.Occurrence) :
    maximal (live xs p.encode) (occurrenceData o)=(OrderedOccurrence.maximal xs p o).encode := by
  rw [OrderedOccurrence.maximal,← all_calibration,live_calibration]
  simp [maximal,List.map_map,Function.comp_def,term_calibration,atMost,Matrix.encode,WindowCode.atMost,WindowCode.negative,WindowCode.less]
theorem dispatch_calibration (xs : List Nat) (p : Formula) :
    dispatch xs p.encode=(OrderedOccurrence.dispatch xs p).map OrderedOccurrence.outputCode := by
  unfold dispatch OrderedOccurrence.dispatch
  rw [NormalFormCodeProof.formula_calibration,inactive_calibration]
  by_cases hx : xs=[]
  · simp [hx,OrderedOccurrence.outputCode]
  by_cases hi : OrderedOccurrence.inactive xs p=[]
  · simp only [hx,hi,if_false,if_true,List.map_append,OrderedOccurrence.ties,OrderedOccurrence.ordered,
      List.map_flatMap,List.map_map,Function.comp_def]
    congr 1
    · apply congrArg (fun f => xs.flatMap f)
      funext i
      apply List.map_congr_left
      intro j hj
      simp only [OrderedOccurrence.outputCode]
      exact WindowCodeProof.matrix_calibration i (.variable j) p.compile
    · apply congrArg (fun f => xs.permutations.flatMap f)
      funext ys
      rw [live_calibration,List.zipIdx_map,List.map_map]
      apply List.map_congr_left
      intro oi hoi
      simp [Function.comp_def,OrderedOccurrence.outputCode,name_calibration,strict_calibration,
        ←maximal_calibration,Matrix.encode,WindowCode.conjunction,live_calibration]
  · simp [hx,hi,OrderedOccurrence.outputCode,List.map_map,Function.comp_def]

end LogicLineages.StandardControlCurrent.OrderedOccurrenceRaw
