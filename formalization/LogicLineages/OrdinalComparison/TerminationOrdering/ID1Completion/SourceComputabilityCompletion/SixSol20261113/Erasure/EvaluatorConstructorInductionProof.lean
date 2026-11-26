module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionIntroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationAtCellsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLambdaAtCellsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationCellsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLambdaCellsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorZeroCellsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel eqn)
open InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorConstructorInductionDefinitions EvaluatorConstructorInductionSyntaxProof
open EvaluatorConstructorCongruenceDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem actualZero (R : Program 2) (H G : Program 1) (M W : Program 2)
 (compat : UniformRetainedCompatibility R H G M W) :
 Nonempty (Derivation body Delta (AtLength R H G M W z)) := by
 apply EvaluatorConstructorInductionIntroProof.actualIntro R H G M W z
 · intro beta j Theta xs hj hf
   simp only [zRelabel] at hf
   exact EvaluatorConstructorApplicationAtCellsProof.actual R H G M W compat z xs hf
     (EvaluatorConstructorZeroCellsProof.actual (OriginalHereditaryEvaluatorDefinitions.evaluator R) (xs 0) (xs 1) (xs 13))
 · intro beta j Theta xs hj hf
   simp only [zRelabel] at hf
   exact EvaluatorConstructorLambdaAtCellsProof.actual R H G M W compat z xs hf
     (EvaluatorConstructorZeroCellsProof.actual (OriginalHereditaryEvaluatorDefinitions.evaluator R) (xs 0) (xs 1) (xs 6))
theorem actualSuccessor (R : Program 2) (H G : Program 1) (M W : Program 2)
 (compat : UniformRetainedCompatibility R H G M W) (count : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowLength R H G M W (suc count)))) :
 Nonempty (Derivation body Delta (AtLength R H G M W (suc count))) := by
 apply EvaluatorConstructorInductionIntroProof.actualIntro R H G M W (suc count)
 · intro beta j Theta xs hj hf
   have hi' := renameInto hi j Theta hj
   simp only [belowLengthRename,sucRelabel] at hi'
   simp only [sucRelabel] at hf
   exact EvaluatorConstructorApplicationAtCellsProof.actual R H G M W compat (suc (count.relabel j)) xs hf
     (EvaluatorConstructorApplicationCellsProof.actualCells R H G M W (count.relabel j) xs hi' hf)
 · intro beta j Theta xs hj hf
   have hi' := renameInto hi j Theta hj
   simp only [belowLengthRename,sucRelabel] at hi'
   simp only [sucRelabel] at hf
   exact EvaluatorConstructorLambdaAtCellsProof.actual R H G M W compat (suc (count.relabel j)) xs hf
     (EvaluatorConstructorLambdaCellsProof.actualCells R H G M W (count.relabel j) xs hi' hf)
theorem actualStep (R : Program 2) (H G : Program 1) (M W : Program 2)
 (compat : UniformRetainedCompatibility R H G M W) (count : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowLength R H G M W count))) :
 Nonempty (Derivation body Delta (AtLength R H G M W count)) := by
 apply zeroSuccessorCases Delta count _
 · have he : Nonempty (Derivation body (eqn count z :: Delta) (eqn count z)) :=
     ⟨Derivation.hypothesis List.mem_cons_self⟩
   exact EvaluatorConstructorInductionTransportProof.atTransport R H G M W z count
     ⟨symm (Classical.choice he)⟩ (actualZero R H G M W compat)
 · intro beta j Theta previous hj he
   rw [atLengthRename]
   have hi' := renameInto hi j Theta hj
   rw [belowLengthRename] at hi'
   have hip := EvaluatorConstructorInductionTransportProof.belowTransport R H G M W
     (count.relabel j) (suc previous) he hi'
   exact EvaluatorConstructorInductionTransportProof.atTransport R H G M W (suc previous) (count.relabel j)
     ⟨symm (Classical.choice he)⟩ (actualSuccessor R H G M W compat previous hip)
theorem actualAtLength (R : Program 2) (H G : Program 1) (M W : Program 2)
 (compat : UniformRetainedCompatibility R H G M W) (count : OTerm alpha) :
 Nonempty (Derivation body Delta (AtLength R H G M W count)) :=
 EvaluatorConstructorInductionBindingProof.lengthInduction R H G M W count
   (fun _ _ n hi => actualStep R H G M W compat n hi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionProof
