module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeRowCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeTokenCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeProof
open PlainBlockLinearizationCode


theorem atoms_calibration (p : BlockRows.Formula) :
    LinearRows.Code.atoms (BlockFormulaSubstitutionCode.formulaCode p) =
      (PlainBlockSplit.atoms p).map (fun a => Encodable.encode (BlockFormulaSubstitutionCode.atomData a)) := by
  induction p with
  | truth => simp [BlockFormulaSubstitutionCode.formulaCode, TiedLinearCodeProof.atoms_step 0 0 (by decide), PlainBlockSplit.atoms]
  | falsity => simp [BlockFormulaSubstitutionCode.formulaCode, TiedLinearCodeProof.atoms_step 0 1 (by decide), PlainBlockSplit.atoms]
  | atom a =>
      simp only [BlockFormulaSubstitutionCode.formulaCode, TiedLinearCodeProof.atoms_step _ 2 (by decide),
        Nat.reduceEqDiff, reduceIte, PlainBlockSplit.atoms, List.map_cons, List.map_nil]
  | negative p hp =>
      simpa only [BlockFormulaSubstitutionCode.formulaCode, TiedLinearCodeProof.atoms_step _ 3 (by decide),
        Nat.reduceEqDiff, reduceIte, PlainBlockSplit.atoms] using hp
  | conjunction p q hp hq =>
      simpa only [BlockFormulaSubstitutionCode.formulaCode, TiedLinearCodeProof.atoms_step _ 4 (by decide),
        Nat.reduceEqDiff, reduceIte, Nat.unpair_pair, PlainBlockSplit.atoms, List.map_append] using
        congrArg₂ (fun a b : List Nat => a ++ b) hp hq
  | disjunction p q hp hq =>
      simpa only [BlockFormulaSubstitutionCode.formulaCode, TiedLinearCodeProof.atoms_step _ 5 (by decide),
        Nat.reduceEqDiff, reduceIte, Nat.unpair_pair, PlainBlockSplit.atoms, List.map_append] using
        congrArg₂ (fun a b : List Nat => a ++ b) hp hq
#print axioms atoms_calibration

theorem all_calibration (ps : List BlockRows.Formula) :
    all (ps.map BlockFormulaSubstitutionCode.formulaCode) =
      BlockFormulaSubstitutionCode.formulaCode (PlainBlockSplit.all ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      change conjunction (BlockFormulaSubstitutionCode.formulaCode p)
        (all (ps.map BlockFormulaSubstitutionCode.formulaCode)) =
          conjunction (BlockFormulaSubstitutionCode.formulaCode p)
            (BlockFormulaSubstitutionCode.formulaCode (PlainBlockSplit.all ps))
      rw [ih]
#print axioms all_calibration

theorem atomCharge_calibration (a : BlockRows.Atom) :
    atomCharge (BlockFormulaSubstitutionCode.atomData a) = PlainBlockSplit.atomCharge a := by
  cases a <;> simp only [atomCharge, BlockFormulaSubstitutionCode.atomData, mass_calibration,
    PlainBlockSplit.atomCharge, BlockRows.Atom.row, Nat.reduceEqDiff, reduceIte]
#print axioms atomCharge_calibration

theorem cutoff_calibration (p : BlockRows.Formula) :
    cutoff (BlockFormulaSubstitutionCode.formulaCode p) = PlainBlockSplit.cutoff p := by
  simp only [cutoff, atoms_calibration, List.map_map, Function.comp_def,
    BlockFormulaSubstitutionCodeProof.decode_atomData, atomCharge_calibration, PlainBlockSplit.cutoff]
#print axioms cutoff_calibration

theorem lowerGuard_calibration (i c : Nat) : lowerGuard i c =
    BlockFormulaSubstitutionCode.formulaCode (PlainBlockSplit.lowerGuard i c) := rfl
#print axioms lowerGuard_calibration

theorem strictMaximumGuard_calibration (i j : Nat) : strictMaximumGuard i j =
    BlockFormulaSubstitutionCode.formulaCode (PlainBlockSplit.strictMaximumGuard i j) := rfl
#print axioms strictMaximumGuard_calibration

theorem frame_calibration (bound : List Nat) (i : Nat) (p : BlockRows.Formula) :
    frame bound i (BlockFormulaSubstitutionCode.formulaCode p) =
      BlockFormulaSubstitutionCode.formulaCode (PlainBlockSplit.frame bound i p) := by
  unfold frame PlainBlockSplit.frame
  rw [cutoff_calibration]
  change conjunction (lowerGuard i (PlainBlockSplit.cutoff p))
    (all ((bound.filter (fun j => j != i)).map (strictMaximumGuard i))) =
      conjunction (BlockFormulaSubstitutionCode.formulaCode (PlainBlockSplit.lowerGuard i (PlainBlockSplit.cutoff p)))
        (BlockFormulaSubstitutionCode.formulaCode (PlainBlockSplit.all
          ((bound.filter (fun j => j != i)).map (PlainBlockSplit.strictMaximumGuard i))))
  rw [← all_calibration]
  apply congrArg₂ conjunction
  · exact lowerGuard_calibration i (PlainBlockSplit.cutoff p)
  · apply congrArg all
    rw [List.map_map]
    apply List.map_congr_left
    intro j hj
    exact strictMaximumGuard_calibration i j
#print axioms frame_calibration

theorem outside_calibration (i : Nat) (p : BlockRows.Formula) :
    outside i (BlockFormulaSubstitutionCode.formulaCode p) =
      BlockFormulaSubstitutionCode.formulaCode (PlainBlockSplit.outside i p) := by
  unfold outside PlainBlockSplit.outside
  rw [atoms_calibration, ← all_calibration, List.map_map, List.map_map]
  apply congrArg all
  apply List.map_congr_left
  intro a ha
  simp only [Function.comp_def, BlockFormulaSubstitutionCodeProof.decode_atomData]
  cases a with
  | nonnegative r => exact outsideRow_calibration i r
  | divisible m r => rfl
#print axioms outside_calibration

theorem linearize_step (i n tag : Nat) (ht : tag < 6) :
    linearize i (6 * n + tag) =
      if tag = 0 then 0 else if tag = 1 then 1
      else if tag = 2 then linearizeAtom i (BlockFormulaSubstitutionCode.decodeAtom n)
      else if tag = 3 then 6 * linearize i n + 3
      else 6 * Nat.pair (linearize i n.unpair.1) (linearize i n.unpair.2) + tag := by
  have hm : (6 * n + tag) % 6 = tag := by omega
  have hd : (6 * n + tag) / 6 = n := by omega
  rw [linearize, hm, hd]
#print axioms linearize_step

theorem linearize_calibration (i : Nat) (p : BlockRows.Formula) :
    linearize i (BlockFormulaSubstitutionCode.formulaCode p) =
      BlockFormulaSubstitutionCode.formulaCode (PlainBlockSplit.linearize i p) := by
  induction p with
  | truth =>
      simpa [BlockFormulaSubstitutionCode.formulaCode, PlainBlockSplit.linearize] using
        linearize_step i 0 0 (by decide)
  | falsity =>
      simpa [BlockFormulaSubstitutionCode.formulaCode, PlainBlockSplit.linearize] using
        linearize_step i 0 1 (by decide)
  | atom a =>
      change linearize i (6 * Encodable.encode (BlockFormulaSubstitutionCode.atomData a) + 2) =
        BlockFormulaSubstitutionCode.formulaCode (PlainBlockSplit.linearize i (.atom a))
      rw [linearize_step _ _ 2 (by decide)]
      simp only [Nat.reduceEqDiff, reduceIte, BlockFormulaSubstitutionCodeProof.decode_atomData]
      cases a with
      | nonnegative r => exact linearizeNonnegative_calibration i r
      | divisible m r => exact residueAtom_calibration m i r
  | negative p hp =>
      simpa [BlockFormulaSubstitutionCode.formulaCode, PlainBlockSplit.linearize, hp] using
        linearize_step i (BlockFormulaSubstitutionCode.formulaCode p) 3 (by decide)
  | conjunction p q hp hq =>
      simpa [BlockFormulaSubstitutionCode.formulaCode, PlainBlockSplit.linearize, Nat.unpair_pair, hp, hq] using
        linearize_step i (Nat.pair (BlockFormulaSubstitutionCode.formulaCode p)
          (BlockFormulaSubstitutionCode.formulaCode q)) 4 (by decide)
  | disjunction p q hp hq =>
      simpa [BlockFormulaSubstitutionCode.formulaCode, PlainBlockSplit.linearize, Nat.unpair_pair, hp, hq] using
        linearize_step i (Nat.pair (BlockFormulaSubstitutionCode.formulaCode p)
          (BlockFormulaSubstitutionCode.formulaCode q)) 5 (by decide)
#print axioms linearize_calibration

theorem literalFormulaCalibration : PlainBlockLinearizationCodeTargets.LiteralFormulaCalibration :=
  fun bound i p => ⟨cutoff_calibration p, frame_calibration bound i p, outside_calibration i p,
    linearize_calibration i p⟩
#print axioms literalFormulaCalibration

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeProof
