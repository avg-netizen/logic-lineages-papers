module
public import LogicLineages.PermittedControl.SignedRowLowStripsTargets
import LogicLineages.PermittedControl.SignedRowCoordinateSliceStatementChecks
import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationGraphProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.SignedRowLowStrips
open OrdinalComparison PreparedProjection SignedRowCoordinateSlice
open MixedSameRankResidue (WeightedOperand WeightedCode encodeWeighted)
open StatementChecks (fixed_signedRowCoordinateSliceCodeExact)

private abbrev Branch := Nat × Result LowerOperandCode

private theorem branchesComputable (f : Nat → Nat) (hf : Computable f) :
    Computable (branchesCode f) := by
  let Input := FamilyArgs × Nat
  have args : Computable (Prod.fst : Input → FamilyArgs) := Computable.fst
  have literalRank : Computable (fun p : Input => p.1.1) := Computable.fst.comp args
  have value : Computable (Prod.snd : Input → Nat) := Computable.snd
  have row : Computable (fun p : Input => p.1.2.2) := Computable.snd.comp (Computable.snd.comp args)
  have result : Computable (fun p : Input => sliceCode f (p.1.1,p.2,p.1.2.2.1,p.1.2.2.2)) :=
    (fixed_signedRowCoordinateSliceCodeExact.1 f hf).comp (literalRank.pair (value.pair row))
  have build : Computable₂ (fun (p : FamilyArgs) (a : Nat) =>
      (a,sliceCode f (p.1,a,p.2.2.1,p.2.2.2))) := (value.pair result).to₂
  let Fold := FamilyArgs × (Nat × List Branch)
  have step : Computable₂ (fun (p : FamilyArgs) (q : Nat × List Branch) =>
      (q.1,sliceCode f (p.1,q.1,p.2.2.1,p.2.2.2)) :: q.2) :=
    (Primrec.list_cons.to_comp.comp
      (build.comp (Computable.fst : Computable (Prod.fst : Fold → FamilyArgs))
        (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).to₂
  have bound : Primrec (fun p : FamilyArgs => p.2.1) := Primrec.fst.comp Primrec.snd
  apply (LayeredComparison.BalancedBoxEvaluation.Graph.computable_foldr (0 : Nat)
    (Primrec.list_range.to_comp.comp bound.to_comp) (Computable.const []) step).of_eq
  rintro ⟨rank,bound,c,terms⟩
  unfold branchesCode
  induction List.range bound with
  | nil => rfl
  | cons a as ih => simp only [List.foldr_cons,List.map_cons,ih]

theorem codeExact : CodeExact := by
  refine ⟨branchesComputable,?_,?_⟩
  · rintro f ⟨rank,bound,c,terms⟩
    simp [branchesCode,List.map_map,Function.comp_def]
  · intro f rank bound c terms
    simp only [branchesCode,branches,List.map_map]
    apply congrArg (fun g : Nat → Branch => (List.range bound).map g)
    funext a
    exact congrArg (fun r : Result LowerOperandCode => (a,r))
      (fixed_signedRowCoordinateSliceCodeExact.2 f rank a c terms)

end LogicLineages.PermittedControl.SignedRowLowStrips
