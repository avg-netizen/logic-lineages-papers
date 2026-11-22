module
public import LogicLineages.PermittedControl.SignedCongruenceMatrixLowStripsTargets
import LogicLineages.PermittedControl.SignedCongruenceMatrixSliceStatementChecks
import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationGraphProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.SignedCongruenceMatrixLowStrips
open OrdinalComparison
open MixedRankNamedResidueRow (RawArgs)
open SharedRankResidueRow (SourceRow encodeRow)
open SignedCongruenceMatrixSlice (sliceRowsCode RawResult)
open StatementChecks (fixed_signedCongruenceMatrixSliceCodeExact)

private theorem branchesComputable (f : Nat → Nat) (hf : Computable f) : Computable (branchesCode f) := by
  let Input := Args × Nat
  have p : Computable (Prod.fst : Input → Args) := Computable.fst
  have rank : Computable (fun q : Input => q.1.1) := Computable.fst.comp p
  have a : Computable (Prod.snd : Input → Nat) := Computable.snd
  have rows : Computable (fun q : Input => q.1.2.2) := Computable.snd.comp (Computable.snd.comp p)
  have slice := (fixed_signedCongruenceMatrixSliceCodeExact.1 f hf).comp (rank.pair (a.pair rows))
  have build : Computable₂ (fun (p : Args) a => (a,sliceRowsCode f (p.1,a,p.2.2))) := (a.pair slice).to₂
  let Step := Args × (Nat × List RawBranch)
  have step : Computable₂ (fun (p : Args) (q : Nat × List RawBranch) =>
      (q.1,sliceRowsCode f (p.1,q.1,p.2.2)) :: q.2) :=
    (Primrec.list_cons.to_comp.comp (build.comp
      (Computable.fst : Computable (Prod.fst : Step → Args)) (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).to₂
  have bound : Primrec (fun p : Args => p.2.1) := Primrec.fst.comp Primrec.snd
  apply (LayeredComparison.BalancedBoxEvaluation.Graph.computable_foldr (0 : Nat)
    (Primrec.list_range.to_comp.comp bound.to_comp) (Computable.const []) step).of_eq
  rintro ⟨rank,bound,rows⟩
  change (List.range bound).foldr (fun a tail => (a,sliceRowsCode f (rank,a,rows)) :: tail) [] =
    (List.range bound).map (fun a => (a,sliceRowsCode f (rank,a,rows)))
  generalize List.range bound = indices
  induction indices with
  | nil => rfl
  | cons a tail ih => simp only [List.foldr_cons,List.map_cons,ih]

theorem codeExact : CodeExact := by
  refine ⟨branchesComputable,?_,?_⟩
  · intro f p
    simp [branchesCode,List.map_map,Function.comp_def]
  · intro f rank bound rows
    simp only [branchesCode,branches,List.map_map]
    apply congrArg (fun g : Nat → RawBranch => (List.range bound).map g)
    funext a
    exact congrArg (fun r : List RawResult => (a,r))
      (fixed_signedCongruenceMatrixSliceCodeExact.2.2 f rank a rows)

end LogicLineages.PermittedControl.SignedCongruenceMatrixLowStrips
