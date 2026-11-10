module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TermCodecProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockFormulaSubstitutionCodeFormulaCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeProof
open TiedLinearCode

theorem summand_data_injective : Function.Injective NormalForm.Summand.data := by
  intro a b h
  cases a <;> cases b <;> simp_all [NormalForm.Summand.data]
#print axioms summand_data_injective

theorem tokenData_injective : Function.Injective tokenData := by
  intro a b h
  cases a with
  | parameter t =>
      cases b with
      | parameter u =>
          exact congrArg TiedLinear.Token.parameter
            (TermCodecProof.originalEncodeInjectivity (congrArg Prod.snd h))
      | occurrence s =>
          have ht := congrArg Prod.fst h
          simp [tokenData] at ht
  | occurrence s =>
      cases b with
      | parameter t =>
          have ht := congrArg Prod.fst h
          simp [tokenData] at ht
      | occurrence t =>
          exact congrArg TiedLinear.Token.occurrence
            (summand_data_injective (Encodable.encode_injective (congrArg Prod.snd h)))
#print axioms tokenData_injective

theorem idxOf_calibration (table : List TiedLinear.Token) (t : TiedLinear.Token) :
    (table.map tokenData).idxOf (tokenData t) = table.idxOf t := by
  induction table with
  | nil => rfl
  | cons a table ih =>
      simp only [List.map_cons]
      by_cases h : a = t
      · subst a
        simp
      · rw [List.idxOf_cons_ne _ (fun he => h (tokenData_injective he)),
          List.idxOf_cons_ne _ h, ih]
#print axioms idxOf_calibration

theorem tokenName_calibration (table : List TiedLinear.Token) (x : Nat)
    (t : TiedLinear.Token) :
    tokenName (table.map tokenData) x (tokenData t) = TiedLinear.tokenName table x t := by
  have h : tokenData t = rawToken x ↔ t = TiedLinear.rawToken x := by
    change tokenData t = tokenData (TiedLinear.rawToken x) ↔ _
    exact tokenData_injective.eq_iff
  unfold tokenName TiedLinear.tokenName
  simp only [h, idxOf_calibration]
#print axioms tokenName_calibration

theorem tokenOfName_calibration (table : List TiedLinear.Token) (x j : Nat) :
    tokenOfName (table.map tokenData) x j = tokenData (TiedLinear.tokenOfName table x j) := by
  unfold tokenOfName TiedLinear.tokenOfName
  by_cases h : j = 0
  · simp only [if_pos h]
    rfl
  · rw [if_neg h, if_neg h, List.getElem?_map]
    cases table[j - 1]? <;> rfl
#print axioms tokenOfName_calibration

theorem rowTokens_calibration (r : BlockRows.Row) :
    rowTokens (BlockRowSubstitutionCode.rowData r) = (TiedLinear.rowTokens r).map tokenData := by
  simp only [rowTokens, BlockRowSubstitutionCode.rowData, TiedLinear.rowTokens,
    List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def, tokenData]
#print axioms rowTokens_calibration

theorem atoms_step (n tag : Nat) (ht : tag < 6) :
    LinearRows.Code.atoms (6 * n + tag) =
      if tag = 0 then [] else if tag = 1 then [] else if tag = 2 then [n]
      else if tag = 3 then LinearRows.Code.atoms n
      else LinearRows.Code.atoms n.unpair.1 ++ LinearRows.Code.atoms n.unpair.2 := by
  have hm : (6 * n + tag) % 6 = tag := by omega
  have hd : (6 * n + tag) / 6 = n := by omega
  rw [LinearRows.Code.atoms, hm, hd]
#print axioms atoms_step

theorem literalTokenCalibration : TiedLinearCodeTargets.LiteralTokenCalibration := by
  intro p
  induction p with
  | truth => simp [tokens, BlockFormulaSubstitutionCode.formulaCode, atoms_step 0 0 (by decide), TiedLinear.tokens]
  | falsity => simp [tokens, BlockFormulaSubstitutionCode.formulaCode, atoms_step 0 1 (by decide), TiedLinear.tokens]
  | atom a =>
      have ha : (BlockFormulaSubstitutionCode.atomData a).2.2 = BlockRowSubstitutionCode.rowData a.row := by
        cases a <;> rfl
      simp only [tokens, BlockFormulaSubstitutionCode.formulaCode, atoms_step _ 2 (by decide),
        Nat.reduceEqDiff, reduceIte, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        BlockFormulaSubstitutionCodeProof.decode_atomData, ha,
        rowTokens_calibration, TiedLinear.tokens]
  | negative p hp =>
      simpa only [tokens, BlockFormulaSubstitutionCode.formulaCode, atoms_step _ 3 (by decide),
        Nat.reduceEqDiff, reduceIte, TiedLinear.tokens] using hp
  | conjunction p q hp hq =>
      simpa only [tokens, BlockFormulaSubstitutionCode.formulaCode, atoms_step _ 4 (by decide),
        Nat.reduceEqDiff, reduceIte, Nat.unpair_pair, List.flatMap_append, TiedLinear.tokens, List.map_append] using
        congrArg₂ (fun a b : List TokenData => a ++ b) hp hq
  | disjunction p q hp hq =>
      simpa only [tokens, BlockFormulaSubstitutionCode.formulaCode, atoms_step _ 5 (by decide),
        Nat.reduceEqDiff, reduceIte, Nat.unpair_pair, List.flatMap_append, TiedLinear.tokens, List.map_append] using
        congrArg₂ (fun a b : List TokenData => a ++ b) hp hq
#print axioms literalTokenCalibration

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeProof
