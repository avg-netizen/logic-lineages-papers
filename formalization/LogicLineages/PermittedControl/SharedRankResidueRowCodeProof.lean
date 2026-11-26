module
public import LogicLineages.PermittedControl.SharedRankResidueRowTargets
import LogicLineages.PermittedControl.SharedRankResidueRowCodeLayoutProof
import LogicLineages.PermittedControl.MixedRankNamedResidueRowSyntaxCodeProof
import LogicLineages.PermittedControl.MixedRankResidueStatementChecks
import LogicLineages.PermittedControl.RankResidueChoicesStatementChecks
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof

@[expose] public section
namespace LogicLineages.PermittedControl.SharedRankResidueRow
open PreparedProjection FiniteStripCollectorRecovery
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof
open RankResidueChoices (Slot Digit Cell choices)
open MixedRankResidue (residueVectorCode residueVector)
open MixedRankNamedResidueRow (RawArgs rawArgs rowFrom toVector clauseCode clauseCodePrimitive clauseCodeLiteral)
open MixedNamedResidueRow (keep)
open StatementChecks (fixed_mixedRankResidueCodeExact fixed_rankResidueLayoutAndChoices)

private abbrev Args := Layout × RawArgs
private abbrev Step := Args × (Cell × Nat)

private theorem formulaStepPrimitive : Primrec₂ (fun (p : Args) (z : Cell × Nat) =>
    if keep p.2.1 (p.2.2.1 + residueVectorCode p.2.2.2 (toVector z.1)) then
      6 * Nat.pair (clauseCode p.2.1 z.1) z.2 + 5 else z.2) := by
  have raw : Primrec (fun p : Step => p.1.2) := Primrec.snd.comp Primrec.fst
  have modulus : Primrec (fun p : Step => p.1.2.1) := Primrec.fst.comp raw
  have constant : Primrec (fun p : Step => p.1.2.2.1) := Primrec.fst.comp (Primrec.snd.comp raw)
  have terms : Primrec (fun p : Step => p.1.2.2.2) := Primrec.snd.comp (Primrec.snd.comp raw)
  have cell : Primrec (fun p : Step => p.2.1) := Primrec.fst.comp Primrec.snd
  have tail : Primrec (fun p : Step => p.2.2) := Primrec.snd.comp Primrec.snd
  have entry : Primrec (fun p : Cell × Digit => p.2.2) := Primrec.snd.comp Primrec.snd
  have vector : Primrec toVector := Primrec.list_map Primrec.id entry.to₂
  have sum := add_primitive.comp constant (fixed_mixedRankResidueCodeExact.2.1.comp terms (vector.comp cell))
  have retained : PrimrecPred (fun p : Step => keep p.1.2.1
      (p.1.2.2.1 + residueVectorCode p.1.2.2.2 (toVector p.2.1)) = true) := by
    simpa only [keep,decide_eq_true_eq] using
      Primrec.eq.comp (Primrec.nat_mod.comp (abs_primitive.comp sum) modulus) (Primrec.const 0)
  have disjunction := Primrec₂.natPair.comp (clauseCodePrimitive.comp modulus cell) tail
  have next := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) disjunction) (Primrec.const 5)
  exact Primrec.ite retained next tail

private theorem preparePrimitive : Primrec prepareCode := by
  have layout : Primrec (Prod.fst : Args → Layout) := Primrec.fst
  have modulus : Primrec (fun p : Args => p.2.1) := Primrec.fst.comp Primrec.snd
  have cells := fixed_rankResidueLayoutAndChoices.2.1.comp modulus layout
  have row : Primrec (fun p : Args => formulaCode p.1 p.2) :=
    Primrec.list_foldr cells (Primrec.const 1) formulaStepPrimitive
  have slotCode : Primrec (fun s : Slot => ((s.1,(0,s.2,(0,0,0,0))) : NamedCode)) :=
    Primrec.fst.pair ((Primrec.const 0).pair (Primrec.snd.pair (Primrec.const (0,0,0,0))))
  have tape := Primrec.list_map layout (slotCode.comp Primrec.snd :
    Primrec (fun p : Args × Slot => ((p.2.1,(0,p.2.2,(0,0,0,0))) : NamedCode))).to₂
  exact Primrec.ite (Primrec.eq.comp modulus (Primrec.const 0)) (Primrec.const none)
    (Primrec.option_some.comp (tape.pair row))

private theorem formulaLiteral (layout : Layout) (r : SourceRow) :
    formulaCode layout (encodeRow r) = (formula layout r).encode := by
  rcases r with ⟨m,c,terms⟩
  simp only [formulaCode,encodeRow,rawArgs,formula,rowFrom,fixed_mixedRankResidueCodeExact.2.2.2,
    clauseCodeLiteral]
  generalize choices m layout = cells
  induction cells with
  | nil => rfl
  | cons cell tail ih =>
    simp only [List.foldr_cons]
    by_cases selected : keep m (c+residueVector terms (toVector cell)) = true
    · simp only [if_pos selected,NormalForm.Formula.encode,ih]
    · simp only [if_neg selected,ih]

theorem codeExact : CodeExact := by
  refine ⟨commonLayoutPrimitive,preparePrimitive,commonLayoutLiteral,?_,?_⟩
  · intro p zero
    simp [prepareCode,zero]
  · intro layout r positive
    have nz : (encodeRow r).1 ≠ 0 := Nat.ne_of_gt positive
    simp [prepareCode,nz,formulaLiteral,requests,List.map_map,Function.comp_def,
      encodeRequest,LowerOperand.code]

end LogicLineages.PermittedControl.SharedRankResidueRow
