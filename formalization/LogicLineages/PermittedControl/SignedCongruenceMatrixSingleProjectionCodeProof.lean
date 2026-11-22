module
public import LogicLineages.PermittedControl.SignedCongruenceMatrixSingleProjectionTargets
import LogicLineages.PermittedControl.HighTailCongruenceMatrixProjectionStatementChecks
import LogicLineages.PermittedControl.SignedCongruenceMatrixLowStripsStatementChecks
import LogicLineages.PermittedControl.SignedCongruenceMatrixStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.SignedCongruenceMatrixSingleProjection
open FiniteStripCollectorRecovery
open MixedRankNamedResidueRow (RawArgs)
open SharedRankResidueRow (encodeRow requests commonLayout)
open SignedCongruenceMatrixLowStrips (branchesCode)
open SignedCongruenceMatrix (commonTail commonTailCode)
open HighTailCongruenceMatrixProjection (projectCode projected)
open StatementChecks (fixed_signedCongruenceMatrixTailExact fixed_signedCongruenceMatrixLowStripsCodeExact
  fixed_highTailCongruenceMatrixProjectionCodeExact)

private theorem compileComputable (f : Nat → Nat) (hf : Computable f) : Computable (compileCode f) := by
  let High := List NamedCode × Nat
  have highInput : Primrec (fun p : Args => ((p.1,p.2.1,p.2.2.2) : HighTailCongruenceMatrixProjection.Args)) :=
    Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have high := (fixed_highTailCongruenceMatrixProjectionCodeExact.1.comp highInput).to_comp
  let Join := Args × High
  have input : Primrec (Prod.fst : Join → Args) := Primrec.fst
  have B : Primrec (fun p : Join => p.1.1) := Primrec.fst.comp input
  have source : Primrec (fun p : Join => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp input)
  have rank : Primrec (fun p : Join => p.1.2.2.1) := Primrec.fst.comp source
  have rows : Primrec (fun p : Join => p.1.2.2.2) := Primrec.snd.comp source
  have cutoff := fixed_signedCongruenceMatrixTailExact.1.comp B rows
  have low := (fixed_signedCongruenceMatrixLowStripsCodeExact.1 f hf).comp (rank.pair (cutoff.pair rows)).to_comp
  exact Computable.option_map high (low.pair Computable.snd).to₂

theorem codeExact : CodeExact := by
  refine ⟨compileComputable,?_,?_⟩
  · intro f B name rank rows
    simp only [compileCode,Option.map_eq_none_iff,fixed_highTailCongruenceMatrixProjectionCodeExact.2.1]
  · intro f B name rank rows positive
    change (projectCode (B,name,rows.map encodeRow)).map _ = _
    rw [fixed_highTailCongruenceMatrixProjectionCodeExact.2.2 B name rows positive]
    change some (branchesCode f (rank,commonTailCode B (rows.map encodeRow),rows.map encodeRow),
      (requests (commonLayout rows)).map encodeRequest,(projected B name rows).encode) = _
    rw [fixed_signedCongruenceMatrixTailExact.2.1,fixed_signedCongruenceMatrixLowStripsCodeExact.2.2]

end LogicLineages.PermittedControl.SignedCongruenceMatrixSingleProjection
