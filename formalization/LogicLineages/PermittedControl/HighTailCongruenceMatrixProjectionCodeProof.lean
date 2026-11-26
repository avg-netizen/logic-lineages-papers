module
public import LogicLineages.PermittedControl.HighTailCongruenceMatrixProjectionTargets
import LogicLineages.PermittedControl.SignedCongruenceMatrixStatementChecks
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.HighTailCongruenceMatrixProjection
open FiniteStripCollectorRecovery
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof
open MixedRankNamedResidueRow (RawArgs)
open SharedRankResidueRow (SourceRow encodeRow commonLayout requests)
open SignedCongruenceMatrix (formula commonTail commonTailCode compileCode)
open HighTailNamedRowProjection (lowerGuardCode)
open StatementChecks (fixed_signedCongruenceMatrixCodeExact fixed_signedCongruenceMatrixTailExact)

private theorem lowerGuardPrimitive : Primrec₂ lowerGuardCode := by
  let Input := Nat × Nat
  have name : Primrec (fun p : Input => p.1) := Primrec.fst
  have lower : Primrec (fun p : Input => p.2) := Primrec.snd
  have shift := negate_primitive.comp (ofNat_primitive.comp lower)
  have variableData : Primrec (fun p : Input => (0,p.1,0,0)) :=
    (Primrec.const 0).pair (name.pair (Primrec.const (0,0)))
  have term := (Primrec.const (1 : Int)).pair variableData
  have terms := Primrec.list_cons.comp term (Primrec.const [])
  have guardData : Primrec (fun p : Input =>
      ((0,0,-(p.2 : Int),[(1,(0,p.1,0,0))]) : NormalForm.Code.AtomData)) :=
    (Primrec.const 0).pair ((Primrec.const 0).pair (shift.pair terms))
  exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6)
    (Primrec.encode.comp guardData)) (Primrec.const 2)

private abbrev Packet := List NamedCode × Nat

private theorem projectPrimitive : Primrec projectCode := by
  let Input := Args × Packet
  have args : Primrec (Prod.fst : Input → Args) := Primrec.fst
  have packet : Primrec (Prod.snd : Input → Packet) := Primrec.snd
  have B : Primrec (fun p : Input => p.1.1) := Primrec.fst.comp args
  have suffix : Primrec (fun p : Input => p.1.2) := Primrec.snd.comp args
  have name : Primrec (fun p : Input => p.1.2.1) := Primrec.fst.comp suffix
  have rows : Primrec (fun p : Input => p.1.2.2) := Primrec.snd.comp suffix
  have tail := fixed_signedCongruenceMatrixTailExact.1.comp B rows
  have guard := lowerGuardPrimitive.comp name tail
  have formulaCode := Primrec.snd.comp packet
  have both := Primrec₂.natPair.comp guard formulaCode
  have guardedCode := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) both) (Primrec.const 4)
  have eliminated := LinearRowsCodeStatementChecks.actual_numeric_programs.2.2.2.comp name guardedCode
  have result := (Primrec.fst.comp packet).pair eliminated
  have prepare : Primrec (fun p : Args => compileCode p.2.2) :=
    fixed_signedCongruenceMatrixCodeExact.1.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.option_map prepare result.to₂

private theorem guardedCodeLiteral (B name : Nat) (rows : List SourceRow) :
    6 * Nat.pair (lowerGuardCode name (commonTail B rows)) (formula rows).encode + 4 =
      (guarded B name rows).encode := rfl

theorem codeExact : CodeExact := by
  refine ⟨projectPrimitive,?_,?_⟩
  · intro B name rows
    simp only [projectCode,Option.map_eq_none_iff,fixed_signedCongruenceMatrixCodeExact.2.1]
  · intro B name rows positive
    change (compileCode (rows.map encodeRow)).map _ = _
    rw [fixed_signedCongruenceMatrixCodeExact.2.2 rows positive]
    change some ((requests (commonLayout rows)).map encodeRequest,LinearRows.Code.eliminate name
      (6 * Nat.pair (lowerGuardCode name (commonTailCode B (rows.map encodeRow))) (formula rows).encode + 4)) =
        some ((requests (commonLayout rows)).map encodeRequest,(LinearRows.eliminate name (guarded B name rows)).encode)
    rw [fixed_signedCongruenceMatrixTailExact.2.1,guardedCodeLiteral,
      LinearRowsCodeStatementChecks.literal_code_calibration.2.2.2]

end LogicLineages.PermittedControl.HighTailCongruenceMatrixProjection
