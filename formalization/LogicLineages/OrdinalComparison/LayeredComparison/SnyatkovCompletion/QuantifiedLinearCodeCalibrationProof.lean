module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.QuantifiedLinearTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.QuantifiedLinearProof
open NormalForm SourceRows

private theorem freeLinear_step (i n tag : Nat) (ht : tag < 4) :
    QuantifiedLinear.Code.freeLinear i (4 * n + tag) =
      if tag = 0 then LinearRows.Code.isLinear i n
      else if tag = 1 then QuantifiedLinear.Code.freeLinear i n
      else if tag = 2 then
        QuantifiedLinear.Code.freeLinear i n.unpair.1 &&
          QuantifiedLinear.Code.freeLinear i n.unpair.2
      else if i = n.unpair.1 then true
      else QuantifiedLinear.Code.freeLinear i n.unpair.2 := by
  have hm : (4 * n + tag) % 4 = tag := by omega
  have hd : (4 * n + tag) / 4 = n := by omega
  rw [QuantifiedLinear.Code.freeLinear, hm, hd]

theorem freeLinear_calibration (i : Nat) (p : QFormula) :
    QuantifiedLinear.Code.freeLinear i p.encode = QuantifiedLinear.freeLinear i p := by
  induction p with
  | matrix p =>
      simpa [QFormula.encode, QuantifiedLinear.freeLinear,
        LinearRowsCodeProof.isLinear_calibration] using freeLinear_step i p.encode 0 (by decide)
  | negative p ih =>
      simpa [QFormula.encode, QuantifiedLinear.freeLinear, ih] using
        freeLinear_step i p.encode 1 (by decide)
  | conjunction p q ihp ihq =>
      simpa [QFormula.encode, QuantifiedLinear.freeLinear, Nat.unpair_pair, ihp, ihq] using
        freeLinear_step i (Nat.pair p.encode q.encode) 2 (by decide)
  | existsNat j p ih =>
      simpa [QFormula.encode, QuantifiedLinear.freeLinear, Nat.unpair_pair, ih] using
        freeLinear_step i (Nat.pair j p.encode) 3 (by decide)

private theorem admissible_step (n tag : Nat) (ht : tag < 4) :
    QuantifiedLinear.Code.admissible (4 * n + tag) =
      if tag = 0 then true
      else if tag = 1 then QuantifiedLinear.Code.admissible n
      else if tag = 2 then
        QuantifiedLinear.Code.admissible n.unpair.1 && QuantifiedLinear.Code.admissible n.unpair.2
      else QuantifiedLinear.Code.admissible n.unpair.2 &&
        QuantifiedLinear.Code.freeLinear n.unpair.1 n.unpair.2 := by
  have hm : (4 * n + tag) % 4 = tag := by omega
  have hd : (4 * n + tag) / 4 = n := by omega
  rw [QuantifiedLinear.Code.admissible, hm, hd]

theorem admissible_calibration (p : QFormula) :
    QuantifiedLinear.Code.admissible p.encode = QuantifiedLinear.admissible p := by
  induction p with
  | matrix p =>
      simpa [QFormula.encode, QuantifiedLinear.admissible] using admissible_step p.encode 0 (by decide)
  | negative p ih =>
      simpa [QFormula.encode, QuantifiedLinear.admissible, ih] using admissible_step p.encode 1 (by decide)
  | conjunction p q ihp ihq =>
      simpa [QFormula.encode, QuantifiedLinear.admissible, Nat.unpair_pair, ihp, ihq] using
        admissible_step (Nat.pair p.encode q.encode) 2 (by decide)
  | existsNat i p ih =>
      simpa [QFormula.encode, QuantifiedLinear.admissible, Nat.unpair_pair, ih,
        freeLinear_calibration] using admissible_step (Nat.pair i p.encode) 3 (by decide)

private theorem eliminate_step (n tag : Nat) (ht : tag < 4) :
    QuantifiedLinear.Code.eliminate (4 * n + tag) =
      if tag = 0 then n
      else if tag = 1 then 6 * QuantifiedLinear.Code.eliminate n + 3
      else if tag = 2 then
        6 * Nat.pair (QuantifiedLinear.Code.eliminate n.unpair.1)
          (QuantifiedLinear.Code.eliminate n.unpair.2) + 4
      else LinearRows.Code.eliminate n.unpair.1 (QuantifiedLinear.Code.eliminate n.unpair.2) := by
  have hm : (4 * n + tag) % 4 = tag := by omega
  have hd : (4 * n + tag) / 4 = n := by omega
  rw [QuantifiedLinear.Code.eliminate, hm, hd]

theorem eliminate_calibration (p : QFormula) :
    QuantifiedLinear.Code.eliminate p.encode = (QuantifiedLinear.eliminate p).encode := by
  induction p with
  | matrix p =>
      simpa [QFormula.encode, QuantifiedLinear.eliminate] using eliminate_step p.encode 0 (by decide)
  | negative p ih =>
      simpa [QFormula.encode, QuantifiedLinear.eliminate, Formula.encode, ih] using
        eliminate_step p.encode 1 (by decide)
  | conjunction p q ihp ihq =>
      simpa [QFormula.encode, QuantifiedLinear.eliminate, Formula.encode, Nat.unpair_pair, ihp, ihq] using
        eliminate_step (Nat.pair p.encode q.encode) 2 (by decide)
  | existsNat i p ih =>
      simpa [QFormula.encode, QuantifiedLinear.eliminate, Nat.unpair_pair, ih,
        LinearRowsCodeProof.eliminate_calibration] using
        eliminate_step (Nat.pair i p.encode) 3 (by decide)

theorem literalCodeCalibration : QuantifiedLinearTargets.LiteralCodeCalibration :=
  ⟨freeLinear_calibration, admissible_calibration, eliminate_calibration⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.QuantifiedLinearProof
