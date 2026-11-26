module
public import LogicLineages.PermittedControl.SignedRowSingleProjectionTargets
import LogicLineages.PermittedControl.HighTailNamedRowProjectionStatementChecks
import LogicLineages.PermittedControl.SignedRowLowStripsStatementChecks
import LogicLineages.PermittedControl.MixedSameRankResidueStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.SignedRowSingleProjection
open FiniteStripCollectorRecovery
open MixedSameRankResidue (encodeWeighted)
open MixedRankNamedResidueRow (RawArgs rawArgs requests)
open HighTailNamedRowProjection (ProjectionArgs coordinateTail projectCode projected)
open SignedRowLowStrips (branchesCode)
open StatementChecks (fixed_highTailNamedRowProjectionCodeExact fixed_signedRowLowStripsCodeExact
  fixed_mixedSameRankResidueCodeExact)

private theorem compileComputable (f : Nat → Nat) (hf : Computable f) : Computable (compileCode f) := by
  have highArgs : Primrec (fun p : Input => ((p.1,p.2.1,p.2.2.2) : ProjectionArgs)) :=
    Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have high := (fixed_highTailNamedRowProjectionCodeExact.1.comp highArgs).to_comp
  let Merge := Input × HighCode
  have idx : Primrec (Prod.fst : Merge → Input) := Primrec.fst
  have B : Primrec (fun p : Merge => p.1.1) := Primrec.fst.comp idx
  have suffix : Primrec (fun p : Merge => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp idx)
  have rank : Primrec (fun p : Merge => p.1.2.2.1) := Primrec.fst.comp suffix
  have raw : Primrec (fun p : Merge => p.1.2.2.2) := Primrec.snd.comp suffix
  have m : Primrec (fun p : Merge => p.1.2.2.2.1) := Primrec.fst.comp raw
  have row : Primrec (fun p : Merge => p.1.2.2.2.2) := Primrec.snd.comp raw
  have terms := Primrec.snd.comp row
  have cutoff := fixed_mixedSameRankResidueCodeExact.2.1.comp (B.pair (m.pair terms))
  have low := (fixed_signedRowLowStripsCodeExact.1 f hf).comp (rank.pair (cutoff.pair row)).to_comp
  exact Computable.option_map high (low.pair Computable.snd).to₂

theorem codeExact : CodeExact := by
  refine ⟨compileComputable,?_,?_⟩
  · rintro f ⟨B,name,rank,q⟩ zero
    change q.1 = 0 at zero
    simp [compileCode,fixed_highTailNamedRowProjectionCodeExact.2.1 (B,name,q) zero]
  · intro f B m name rank c terms positive
    change (projectCode (B,name,rawArgs m c terms)).map _ = _
    rw [fixed_highTailNamedRowProjectionCodeExact.2.2 B m name c terms positive]
    change some (branchesCode f (rank,coordinateTail B m terms,c,terms.map encodeWeighted),
      (requests terms).map encodeRequest,(projected B m name c terms).encode) = _
    rw [fixed_signedRowLowStripsCodeExact.2.2]

end LogicLineages.PermittedControl.SignedRowSingleProjection
