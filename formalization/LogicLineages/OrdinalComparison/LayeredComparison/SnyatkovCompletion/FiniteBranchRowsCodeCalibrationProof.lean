module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteBranchRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsCodeCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteBranchRowsCodeProof
open NormalForm (Summand Row rowData Atom Formula domainFormula guardedAtom)
open FiniteBranchRows

theorem nonlinear_calibration (i : Nat) (kind : Bool) (e h : Int) :
    Code.nonlinear i kind e h = (nonlinear i kind e h).data := by
  cases kind <;> rfl

theorem leRow_calibration (s t : Summand) (c : Nat) :
    Code.leRow s.data t.data c = rowData (leRow s t c) := rfl

theorem nonnegative_calibration (row : Row) :
    Code.nonnegative (rowData row) = (Formula.atom (.nonnegative row)).encode := rfl

/-- Domain clauses are coded in the same radix-six normal form as the matrix;
each original summand occurrence contributes its own literal cutoff row. -/
theorem domains_calibration (row : Row) :
    Code.domains (rowData row) = (domainFormula row).encode := by
  rcases row with ⟨z, xs⟩
  change (xs.map (fun a => (a.1, a.2.data))).foldr
      (fun a rest => Code.conjunction
        (Code.nonnegative (NormalForm.Code.domainRowData a.2)) rest) 0 =
    (xs.foldr (fun a rest => Formula.conjunction
      (.atom (.nonnegative (NormalForm.domainRow a.2))) rest) .truth).encode
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.map_cons, List.foldr_cons, Formula.encode]
      rw [NormalFormCodeProof.domain_data, ih, nonnegative_calibration]
      rfl

theorem guardedLe_calibration (s t : Summand) (c : Nat) :
    Code.guardedLe s.data t.data c = (guardedLe s t c).encode := by
  unfold Code.guardedLe
  rw [leRow_calibration, domains_calibration, nonnegative_calibration]
  rfl

theorem linearGuard_calibration (i j : Nat) (lk rk : Bool)
    (e h k l : Int) (a code : Nat) :
    Code.linearGuard (LinearWindow.Code.input i j lk rk e h k l a code) =
      (linearGuard i j lk rk e h k l a).encode := by
  change Code.conjunction
    (Code.guardedLe (Code.nonlinear j rk k l) (Code.nonlinear i lk e h) 1)
    (Code.guardedLe (Code.nonlinear i lk e h) (Summand.variable j).data a) = _
  simp only [nonlinear_calibration, guardedLe_calibration]
  rfl

theorem activeGuard_calibration (i j : Nat) (kind : Bool)
    (e h k l q : Int) (a code : Nat) :
    Code.activeGuard (ActiveHyper.Code.input i j kind e h k l q a code) =
      (activeGuard i j kind e h k l q a).encode := by
  change Code.conjunction
    (Code.guardedLe (Summand.hyperPhi j k l).data (Code.nonlinear i kind e h) 1)
    (Code.guardedLe (Code.nonlinear i kind e h) (Summand.phi j q).data a) = _
  simp only [nonlinear_calibration, guardedLe_calibration]
  rfl

theorem linearCases_calibration (i j : Nat) (lk rk : Bool)
    (e h k l : Int) (a : Nat) (p : Formula) :
    Code.linearCases (LinearWindow.Code.input i j lk rk e h k l a p.encode) =
      (linearCases i j lk rk e h k l a p).encode := by
  change BoundedRows.Code.bounded j (LinearWindow.bound rk k l a)
    (Code.conjunction (Code.linearGuard (LinearWindow.Code.input i j lk rk e h k l a p.encode))
      p.encode) = _
  rw [linearGuard_calibration]
  exact BoundedRowsCodeProof.bounded_calibration j (LinearWindow.bound rk k l a)
    (.conjunction (linearGuard i j lk rk e h k l a) p)

theorem activeCases_calibration (i j : Nat) (kind : Bool)
    (e h k l q : Int) (a : Nat) (p : Formula) :
    Code.activeCases (ActiveHyper.Code.input i j kind e h k l q a p.encode) =
      (activeCases i j kind e h k l q a p).encode := by
  change BoundedRows.Code.bounded j (ActiveHyper.bound k l q a)
    (Code.conjunction (Code.activeGuard (ActiveHyper.Code.input i j kind e h k l q a p.encode))
      p.encode) = _
  rw [activeGuard_calibration]
  exact BoundedRowsCodeProof.bounded_calibration j (ActiveHyper.bound k l q a)
    (.conjunction (activeGuard i j kind e h k l q a) p)

theorem literalBranchCodeCalibration : FiniteBranchRowsTargets.LiteralBranchCodeCalibration :=
  ⟨linearCases_calibration, activeCases_calibration⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteBranchRowsCodeProof
