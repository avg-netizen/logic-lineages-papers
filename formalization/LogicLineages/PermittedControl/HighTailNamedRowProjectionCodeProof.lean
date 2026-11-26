module
public import LogicLineages.PermittedControl.HighTailNamedRowProjectionTargets
import LogicLineages.PermittedControl.MixedRankNamedResidueRowStatementChecks
import LogicLineages.PermittedControl.MixedSameRankResidueStatementChecks
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.HighTailNamedRowProjection
open FiniteStripCollectorRecovery
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof
open MixedSameRankResidue (WeightedOperand WeightedCode encodeWeighted weightedTailCode)
open MixedRankNamedResidueRow (RawArgs rawArgs prepareCode requests row)
open StatementChecks (fixed_mixedRankNamedResidueRowCodeExact fixed_mixedSameRankResidueCodeExact)

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
  let Input := ProjectionArgs × Packet
  have args : Primrec (Prod.fst : Input → ProjectionArgs) := Primrec.fst
  have packet : Primrec (Prod.snd : Input → Packet) := Primrec.snd
  have B : Primrec (fun p : Input => p.1.1) := Primrec.fst.comp args
  have rest : Primrec (fun p : Input => p.1.2) := Primrec.snd.comp args
  have name : Primrec (fun p : Input => p.1.2.1) := Primrec.fst.comp rest
  have raw : Primrec (fun p : Input => p.1.2.2) := Primrec.snd.comp rest
  have m : Primrec (fun p : Input => p.1.2.2.1) := Primrec.fst.comp raw
  have terms : Primrec (fun p : Input => p.1.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp raw)
  have tail := fixed_mixedSameRankResidueCodeExact.2.1.comp (B.pair (m.pair terms))
  have guard := lowerGuardPrimitive.comp name tail
  have p := Primrec.snd.comp packet
  have both := Primrec₂.natPair.comp guard p
  have guardedCode := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) both) (Primrec.const 4)
  have eliminated := LinearRowsCodeStatementChecks.actual_numeric_programs.2.2.2.comp name guardedCode
  have result := (Primrec.fst.comp packet).pair eliminated
  have prepare : Primrec (fun p : ProjectionArgs => prepareCode p.2.2) :=
    fixed_mixedRankNamedResidueRowCodeExact.1.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.option_map prepare result.to₂

private theorem guardedCodeLiteral (B m name : Nat) (c : Int) (terms : List WeightedOperand) :
    6 * Nat.pair (lowerGuardCode name (coordinateTail B m terms)) (row m c terms).encode + 4 =
      (guarded B m name c terms).encode := rfl

theorem codeExact : CodeExact := by
  refine ⟨projectPrimitive,?_,?_⟩
  · rintro ⟨B,name,q⟩ zero
    change q.1 = 0 at zero
    simp [projectCode,fixed_mixedRankNamedResidueRowCodeExact.2.1 q zero]
  · intro B m name c terms positive
    change (prepareCode (rawArgs m c terms)).map _ = _
    rw [fixed_mixedRankNamedResidueRowCodeExact.2.2 m c terms positive]
    change some ((requests terms).map encodeRequest,LinearRows.Code.eliminate name
      (6 * Nat.pair (lowerGuardCode name (coordinateTail B m terms)) (row m c terms).encode + 4)) =
        some ((requests terms).map encodeRequest,(LinearRows.eliminate name (guarded B m name c terms)).encode)
    rw [guardedCodeLiteral,LinearRowsCodeStatementChecks.literal_code_calibration.2.2.2]

end LogicLineages.PermittedControl.HighTailNamedRowProjection
