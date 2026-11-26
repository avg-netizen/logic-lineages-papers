module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericPlainTerminalTargets
import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericPlainTerminalPrimitiveProof
import LogicLineages.PermittedControl.OriginalMixedTerminalTestReadProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeCalibrationProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsCodeStatementChecks
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsSemanticProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuationCalibrationProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuationSemanticProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNumericPlainTerminal
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitNumericRead (bank)
open OriginalMixedTerminalTest (Test exactTerminalTestRead)
open NormalForm (Formula Atom)

private theorem originalVariablesFromAtoms (p : Formula) :
    p.variables = (LinearRows.atoms p).flatMap (fun a => NormalForm.rowVariables a.row) := by
  induction p <;> simp [Formula.variables,LinearRows.atoms,*]

private theorem atomDataRow (a : Atom) : a.data.2.2 = NormalForm.rowData a.row := by
  cases a <;> rfl

private theorem termDataName (s : NormalForm.Summand) : s.data.2.1 = s.name := by
  cases s <;> rfl

private theorem decodedAtomData (a : Atom) :
    LinearRows.Code.decodeAtom (Encodable.encode a.data) = a.data := by
  simp only [LinearRows.Code.decodeAtom,Encodable.encodek,Option.getD_some]

/-- The same literal name inventory as the original raw program. No
comparison/cutoff or residue theorem is needed for this syntax fact. -/
private theorem rawVariablesExact (p : Formula) :
    MaximalPlainBranchPrograms.Code.variables p.encode = p.variables := by
  rw [originalVariablesFromAtoms p]
  simp only [MaximalPlainBranchPrograms.Code.variables,LinearRowsCodeProof.atoms_calibration,
    List.flatMap_map,Function.comp_def,decodedAtomData,atomDataRow,NormalForm.rowData,
    NormalForm.rowVariables,List.map_map,termDataName]

private theorem atomVariablesOnlyExact (a : Atom) :
    atomVariablesOnly (Encodable.encode a.data) = true ↔
      ∀ t ∈ a.row.2, ∃ i : Nat, t.2 = .variable i := by
  have decoded : LinearRows.Code.decodeAtom (Encodable.encode a.data) = a.data := by
    simp only [LinearRows.Code.decodeAtom,Encodable.encodek,Option.getD_some]
  have shape : a.data.2.2 = NormalForm.rowData a.row := by cases a <;> rfl
  simp only [atomVariablesOnly,decoded,shape,NormalForm.rowData,List.all_map,Function.comp_def,
    List.all_eq_true,decide_eq_true_eq]
  constructor
  · intro h t ht
    have tag := h t ht
    cases rule : t.2 with
    | variable i => exact ⟨i,rule⟩
    | phi i e => simp [rule,NormalForm.Summand.data] at tag
    | hyperPhi i e h => simp [rule,NormalForm.Summand.data] at tag
  · intro h t ht
    obtain ⟨i,hi⟩ := h t ht
    simp [hi,NormalForm.Summand.data]

private theorem variablesOnlyExact (p : Formula) :
    variablesOnly p.encode = true ↔ (Test.rows p).Admitted := by
  simp only [variablesOnly,LinearRowsCodeProof.atoms_calibration,List.all_map,Function.comp_def,
    List.all_eq_true,atomVariablesOnlyExact,Test.Admitted,PreparedProjection.PlainPreparedFormula]

private theorem plainGuardExact (values : List Nat) (p : Formula) :
    plainGuard (values,p.encode) = true ↔
      (Test.rows p).Admitted ∧ ∀ n ∈ p.variables, n < values.length := by
  simp only [plainGuard,Bool.and_eq_true_iff,namesFit,List.all_eq_true,decide_eq_true_eq,
    rawVariablesExact,variablesOnlyExact]

private def frozen (values : List Nat) (names : List Nat) (p : Formula) : Formula :=
  names.foldr (fun n r => BoundedRows.substitute n (bank values n) r) p

private def installValues (values : List Nat) (names : List Nat) (θ : Nat → Nat) : Nat → Nat :=
  names.foldl (fun ν n => Function.update ν n (bank values n)) θ

private theorem freezeCode (values names : List Nat) (p : Formula) :
    names.foldr (fun n r => BoundedRows.Code.formula n (bank values n) r) p.encode =
      (frozen values names p).encode := by
  induction names with
  | nil => rfl
  | cons n ns ih =>
      change BoundedRows.Code.formula n (bank values n)
        (ns.foldr (fun k r => BoundedRows.Code.formula k (bank values k) r) p.encode) =
          (BoundedRows.substitute n (bank values n) (frozen values ns p)).encode
      rw [ih]
      exact BoundedRowsCodeStatementChecks.literal_code_calibration.2.2.1 _ _ _

private theorem freezeEval (values names : List Nat) (p : Formula) (θ : Nat → Nat) :
    (frozen values names p).eval θ ↔ p.eval (installValues values names θ) := by
  induction names generalizing θ with
  | nil => rfl
  | cons n ns ih =>
      exact (BoundedRowsSemanticProof.actualFormulaSubstitution n (bank values n)
        (frozen values ns p) θ).trans (ih (Function.update θ n (bank values n)))

private theorem installed (values names : List Nat) (θ : Nat → Nat) (n : Nat) :
    installValues values names θ n = if n ∈ names then bank values n else θ n := by
  induction names generalizing θ with
  | nil => simp [installValues]
  | cons a as ih =>
      change installValues values as (Function.update θ a (bank values a)) n = _
      rw [ih]
      by_cases tail : n ∈ as
      · simp [tail,List.mem_cons]
      · by_cases head : n = a
        · subst n
          simp [tail,Function.update_self]
        · simp [tail,head,List.mem_cons,Function.update_of_ne head]

private theorem plainAnswerExact (values : List Nat) (p : Formula) (hp : (Test.rows p).Admitted) :
    plainAnswer (values,p.encode) = (Test.rows p).answer (bank values) := by
  have hBool := exactTerminalTestRead (.rows p) hp (bank values) true
  have unchanged : ∀ n ∈ p.variables, installValues values p.variables (fun _ => 0) n = bank values n := by
    intro n hn
    rw [installed,if_pos hn]
  have exactEval : plainAnswer (values,p.encode) = true ↔ p.eval (bank values) := by
    unfold plainAnswer
    change ZeroValuation.Code.evaluate ((MaximalPlainBranchPrograms.Code.variables p.encode).foldr
      (fun n r => BoundedRows.Code.formula n (bank values n) r) p.encode) = true ↔ _
    rw [rawVariablesExact,freezeCode,
      ZeroValuationProof.literalCodeCalibration.2.2.2]
    exact (ZeroValuationProof.actualZeroEvaluator _).trans
      ((freezeEval values p.variables p (fun _ => 0)).trans
        (SourceTermGraphSupportProof.formula_eval_congr p _ _ unchanged))
  apply Bool.eq_iff_iff.mpr
  exact exactEval.trans hBool.symm

theorem exactPlainTerminalData : ExactPlainTerminalData :=
  ⟨namesFitPrimitive,plainGuardPrimitive,plainAnswerPrimitive,plainGuardExact,plainAnswerExact⟩

end LogicLineages.PermittedControl.OriginalPrintedCircuitNumericPlainTerminal
