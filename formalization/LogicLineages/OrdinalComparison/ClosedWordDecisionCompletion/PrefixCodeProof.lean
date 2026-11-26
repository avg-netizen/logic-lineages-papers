module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.CodeAdapterProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.CodeProof
open PolynomialGraphCompletion WordLinearDecisionCompletion RankedWordDecisionCompletion

theorem prefix_calibration (floor N : Nat) (p : Formula) :
    Code.prefixChildren floor N (Formula.encode p) =
      (prefixChildren floor N p).map (fun b => (b.1,Formula.encode b.2)) := by
  simp only [Code.prefixChildren,names_calibration,prefixChildren,List.map_flatMap,
    List.map_filterMap,Function.comp_def]
  apply congrArg (fun f : Nat → List (Nat × Nat) => (names p).flatMap f)
  funext x
  apply congrArg (fun f : Nat → Option (Nat × Nat) => (List.range (N-floor)).filterMap f)
  funext k
  have hc := OriginalWordEvaluation.Proof.literalCodeCalibration x (floor+k) p
  rw [hc.1,hc.2]
  split <;> rfl

#print axioms prefix_calibration

end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.CodeProof
