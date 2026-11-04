module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCodeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCodeProof

private theorem term_step (i r n tag : Nat) (ht : tag < 10) :
    WindowCode.termSubstitute i r (10 * n + tag) =
      if tag = 0 then 10 * n + tag
      else if tag = 1 then if n = i then r else 10 * n + tag
      else if tag = 2 ∨ tag = 3 then
        10 * Nat.pair (WindowCode.termSubstitute i r n.unpair.1)
          (WindowCode.termSubstitute i r n.unpair.2) + tag
      else if tag = 4 ∨ tag = 5 then
        10 * Nat.pair n.unpair.1 (WindowCode.termSubstitute i r n.unpair.2) + tag
      else 10 * WindowCode.termSubstitute i r n + tag := by
  have hm : (10 * n + tag) % 10 = tag := by omega
  have hd : (10 * n + tag) / 10 = n := by omega
  rw [WindowCode.termSubstitute, hm, hd]

theorem term_calibration (i : Nat) (r a : Term) :
    WindowCode.termSubstitute i r.encode a.encode = (a.substitute i r).encode := by
  induction a with
  | numeral n =>
    simpa [Term.encode, Term.substitute] using term_step i r.encode n 0 (by decide)
  | «variable» j =>
    by_cases h : j = i <;>
      simpa [Term.encode, Term.substitute, h] using term_step i r.encode j 1 (by decide)
  | add a b ha hb =>
    simpa [Term.encode, Term.substitute, Nat.unpair_pair, ha, hb] using
      term_step i r.encode (Nat.pair a.encode b.encode) 2 (by decide)
  | subtract a b ha hb =>
    simpa [Term.encode, Term.substitute, Nat.unpair_pair, ha, hb] using
      term_step i r.encode (Nat.pair a.encode b.encode) 3 (by decide)
  | multiply c a ha =>
    simpa [Term.encode, Term.substitute, Nat.unpair_pair, ha] using
      term_step i r.encode (Nat.pair c a.encode) 4 (by decide)
  | divide c a ha =>
    simpa [Term.encode, Term.substitute, Nat.unpair_pair, ha] using
      term_step i r.encode (Nat.pair c a.encode) 5 (by decide)
  | phi a ha =>
    simpa [Term.encode, Term.substitute, ha] using term_step i r.encode a.encode 6 (by decide)
  | hyper a ha =>
    simpa [Term.encode, Term.substitute, ha] using term_step i r.encode a.encode 7 (by decide)
  | phiInverse a ha =>
    simpa [Term.encode, Term.substitute, ha] using term_step i r.encode a.encode 8 (by decide)
  | hyperInverse a ha =>
    simpa [Term.encode, Term.substitute, ha] using term_step i r.encode a.encode 9 (by decide)

private theorem matrix_step (i r n tag : Nat) (ht : tag < 8) :
    WindowCode.matrixSubstitute i r (8 * n + tag) =
      if tag = 0 then 0
      else if tag = 1 then 1
      else if tag = 2 ∨ tag = 3 then
        8 * Nat.pair (WindowCode.termSubstitute i r n.unpair.1)
          (WindowCode.termSubstitute i r n.unpair.2) + tag
      else if tag = 4 then
        8 * Nat.pair n.unpair.1 (WindowCode.termSubstitute i r n.unpair.2) + 4
      else if tag = 5 then 8 * WindowCode.matrixSubstitute i r n + 5
      else 8 * Nat.pair (WindowCode.matrixSubstitute i r n.unpair.1)
        (WindowCode.matrixSubstitute i r n.unpair.2) + tag := by
  have hm : (8 * n + tag) % 8 = tag := by omega
  have hd : (8 * n + tag) / 8 = n := by omega
  rw [WindowCode.matrixSubstitute, hm, hd]

theorem matrix_calibration (i : Nat) (r : Term) (p : Matrix) :
    WindowCode.matrixSubstitute i r.encode p.encode = (p.substitute i r).encode := by
  induction p with
  | truth =>
    simpa [Matrix.encode, Matrix.substitute] using matrix_step i r.encode 0 0 (by decide)
  | falsity =>
    simpa [Matrix.encode, Matrix.substitute] using matrix_step i r.encode 0 1 (by decide)
  | equal a b =>
    simpa [Matrix.encode, Matrix.substitute, Nat.unpair_pair, term_calibration] using
      matrix_step i r.encode (Nat.pair a.encode b.encode) 2 (by decide)
  | less a b =>
    simpa [Matrix.encode, Matrix.substitute, Nat.unpair_pair, term_calibration] using
      matrix_step i r.encode (Nat.pair a.encode b.encode) 3 (by decide)
  | divisible m a =>
    simpa [Matrix.encode, Matrix.substitute, Nat.unpair_pair, term_calibration] using
      matrix_step i r.encode (Nat.pair m a.encode) 4 (by decide)
  | negative p hp =>
    simpa [Matrix.encode, Matrix.substitute, hp] using matrix_step i r.encode p.encode 5 (by decide)
  | conjunction p q hp hq =>
    simpa [Matrix.encode, Matrix.substitute, Nat.unpair_pair, hp, hq] using
      matrix_step i r.encode (Nat.pair p.encode q.encode) 6 (by decide)
  | disjunction p q hp hq =>
    simpa [Matrix.encode, Matrix.substitute, Nat.unpair_pair, hp, hq] using
      matrix_step i r.encode (Nat.pair p.encode q.encode) 7 (by decide)

private theorem any_calibration (xs : List Matrix) :
    WindowCode.any (xs.map Matrix.encode) = (Matrix.any xs).encode := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    change 8 * Nat.pair p.encode (WindowCode.any (ps.map Matrix.encode)) + 7 =
      8 * Nat.pair p.encode (Matrix.any ps).encode + 7
    rw [ih]

theorem finite_calibration (i : Nat) (a : Term) (e : Int) (c : Nat) (p : Matrix) :
    WindowCode.finiteWindow (i, a.encode, e, c, p.encode) =
      (finiteWindow i a e c p).encode := by
  unfold WindowCode.finiteWindow finiteWindow
  rw [← any_calibration]
  apply congrArg WindowCode.any
  rw [List.map_map]
  apply List.map_congr_left
  intro d hd
  exact matrix_calibration i (replacementTerm a e d)
    (Matrix.conjunction (closeMatrix i a e c) p)

theorem literalCalibration : WindowCodeTargets.LiteralCalibration :=
  ⟨term_calibration, matrix_calibration, finite_calibration⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCodeProof
