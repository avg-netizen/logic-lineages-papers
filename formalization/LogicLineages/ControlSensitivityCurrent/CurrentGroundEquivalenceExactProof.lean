module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundEquivalenceSemanticProof
public import LogicLineages.ControlSensitivityCurrent.CurrentCompilerOutputProof
public import LogicLineages.ControlSensitivityCurrent.RawBinaryPlanProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundEquivalence

open LogicLineages.OrdinalComparison.Source GroundEquivalence ExistentialPlan
open RawSourceDAG

theorem counterexample_code (weakQuery : Bool) (n : Nat)
    (a b : Input (List.replicate n Ty.ground) .ground) :
    counterexampleCode weakQuery n (encode ⟨_,.ground,a⟩) (encode ⟨_,.ground,b⟩) =
      InputCompiler.encodeInput (counterexample weakQuery a b) := by
  let Γ := List.replicate n Ty.ground
  have hc : Γ.map SyntaxCode.typeCode = List.replicate n 0 := CurrentCompiler.ground_context_code n
  have ht := BinaryPlanCompiler.prefix_table_code Γ 1
  rw [hc] at ht
  have hr : Operations.renameCode (0 :: List.replicate n 0)
      (Operations.renamingCode (PrimitiveLowering.shift 1 (Γ := Γ))) (encode ⟨Γ,.ground,b⟩) =
      encode ⟨.ground :: Γ,.ground,ScopedDAG.renameInput (Renaming.weaken Γ .ground) b⟩ := by
    rw [← hc]
    exact (Operations.rename_input (Renaming.weaken Γ .ground) b).symm
  dsimp only [Γ] at ht hr
  cases weakQuery <;> simp only [counterexampleCode, ht, hr] <;> rfl

theorem exact_reductions : CurrentGroundEquivalenceTargets.ExactReductions := by
  intro n a b
  dsimp only
  have hcw := counterexample_code true n a b
  have hcs := counterexample_code false n a b
  have hw := (CurrentCompiler.literal_outputs.1 n (counterexample true a b)).2
  have hs := (CurrentCompiler.literal_outputs.1 n (counterexample false a b)).2
  have houtw : reduce true n (encode ⟨_,.ground,a⟩) (encode ⟨_,.ground,b⟩) =
      RawPlanComparisonTargets.encodeComparison
        (BooleanCompiler.strictPair (InputNormalization.normalize .nil (counterexample true a b))) := by
    simp only [reduce,hcw,hw,CurrentCompiler.expected,ite_true]
  have houts : reduce false n (encode ⟨_,.ground,a⟩) (encode ⟨_,.ground,b⟩) =
      RawPlanComparisonTargets.encodeComparison
        (BooleanCompiler.weakPair (InputNormalization.normalize .nil (counterexample false a b))) := by
    simp only [reduce,hcs,hs,CurrentCompiler.expected,Bool.false_eq_true,ite_false]
  have bw := CompilerComposition.outputBudgets.2 n (counterexample true a b)
  have bs := CompilerComposition.outputBudgets.2 n (counterexample false a b)
  have hb (flag : Bool) : (counterexample flag a b).cost = 6 ∧
      (counterexample flag a b).sourceMax = max a.specs.length b.specs.length := by
    cases flag <;> simp [counterexample,InputNormalization.Input.cost,
      InputNormalization.Input.sourceMax,ScopedDAG.renameInput]
  rw [(hb true).1,(hb true).2] at bw
  rw [(hb false).1,(hb false).2] at bs
  exact ⟨hcw,hcs,houtw,houts,reductions_semantic n a b,bw.1,bs.1,bw.2.1,bw.2.2.1,
    bs.2.2.2.1,bs.2.2.2.2⟩

end LogicLineages.ControlSensitivityCurrent.CurrentGroundEquivalence
