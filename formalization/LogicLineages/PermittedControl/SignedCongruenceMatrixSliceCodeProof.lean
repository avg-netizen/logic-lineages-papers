module
public import LogicLineages.PermittedControl.SignedCongruenceMatrixSliceTargets
import LogicLineages.PermittedControl.SignedRowCoordinateSliceStatementChecks
import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationGraphProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.SignedCongruenceMatrixSlice
open OrdinalComparison
open MixedSameRankResidue (encodeWeighted)
open MixedRankNamedResidueRow (RawArgs rawArgs)
open SharedRankResidueRow (SourceRow encodeRow)
open SignedRowCoordinateSlice (sliceCode)
open StatementChecks (fixed_signedRowCoordinateSliceCodeExact)

private theorem sliceRowsComputable (f : Nat → Nat) (hf : Computable f) : Computable (sliceRowsCode f) := by
  let Input := Args × RawArgs
  have config : Computable (Prod.fst : Input → Args) := Computable.fst
  have row : Computable (Prod.snd : Input → RawArgs) := Computable.snd
  have rank : Computable (fun p : Input => p.1.1) := Computable.fst.comp config
  have a : Computable (fun p : Input => p.1.2.1) := Computable.fst.comp (Computable.snd.comp config)
  have content : Computable (fun p : Input => p.2.2) := Computable.snd.comp row
  have m : Computable (fun p : Input => p.2.1) := Computable.fst.comp row
  have result := (fixed_signedRowCoordinateSliceCodeExact.1 f hf).comp (rank.pair (a.pair content))
  have build : Computable₂ (fun (p : Args) (r : RawArgs) =>
      (r.1,sliceCode f (p.1,p.2.1,r.2.1,r.2.2))) := (m.pair result).to₂
  let Step := Args × (RawArgs × List RawResult)
  have step : Computable₂ (fun (p : Args) (q : RawArgs × List RawResult) =>
      (q.1.1,sliceCode f (p.1,p.2.1,q.1.2.1,q.1.2.2)) :: q.2) :=
    (Primrec.list_cons.to_comp.comp (build.comp
      (Computable.fst : Computable (Prod.fst : Step → Args)) (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).to₂
  have rows : Computable (fun p : Args => p.2.2) := Computable.snd.comp Computable.snd
  apply (LayeredComparison.BalancedBoxEvaluation.Graph.computable_foldr (default : RawArgs)
    rows (Computable.const []) step).of_eq
  rintro ⟨rank,a,rs⟩
  change rs.foldr (fun r tail => (r.1,sliceCode f (rank,a,r.2.1,r.2.2)) :: tail) [] =
    rs.map (fun r => (r.1,sliceCode f (rank,a,r.2.1,r.2.2)))
  induction rs with
  | nil => rfl
  | cons r tail ih => simp only [List.foldr_cons,List.map_cons,ih]

theorem codeExact : CodeExact := by
  refine ⟨sliceRowsComputable,?_,?_⟩
  · intro f p
    simp [sliceRowsCode,List.map_map,Function.comp_def]
  · intro f rank a rows
    simp only [sliceRowsCode,sliceRows,List.map_map]
    apply congrArg (fun g : SourceRow → RawResult => rows.map g)
    funext r
    change (r.1,sliceCode f (rank,a,r.2.1,r.2.2.map encodeWeighted)) =
      (r.1,(SignedRowCoordinateSlice.slice f rank a r.2.1 r.2.2).map
        (Option.map SignedRowCoordinateSlice.encodeResidual))
    rw [fixed_signedRowCoordinateSliceCodeExact.2]

end LogicLineages.PermittedControl.SignedCongruenceMatrixSlice
