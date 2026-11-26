module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFuelProgramTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeCodeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportEvaluationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsEvaluationProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFuelProgramProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalHereditaryFuelProgram
open OriginalRawSyntaxTransportEvaluationSupportProof (constantEvaluation succOfEvaluation)
open InternalApplicationCertificateConstructorsEvaluationProof (leftOfEvaluation rightOfEvaluation)
open InternalArithmeticProgramsEvaluationProof (exactAdditionEvaluation exactMultiplicationEvaluation)
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo)
attribute [local irreducible] InternalArithmeticPrograms.addition InternalArithmeticPrograms.multiplication
 OriginalStructuralNodeSize.raw OriginalContextInsertion.length

theorem addEvaluation (x y : Nat) : evaluate InternalArithmeticPrograms.addition (x ::ᵥ y ::ᵥ nil) = x+y := exactAdditionEvaluation x y
theorem mulEvaluation (x y : Nat) : evaluate InternalArithmeticPrograms.multiplication (x ::ᵥ y ::ᵥ nil) = x*y := exactMultiplicationEvaluation x y

theorem budgetStepEvaluation (depth previous branching : Nat) :
 evaluate budgetStep (depth ::ᵥ previous ::ᵥ branching ::ᵥ nil) = 1 + branching * previous := by
 simp only [budgetStep,succOfEvaluation,evaluate,vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one]
 change Nat.succ (evaluate InternalArithmeticPrograms.multiplication (branching ::ᵥ previous ::ᵥ nil)) = _
 rw [mulEvaluation]
 omega

theorem budgetEvaluation (depth branching : Nat) :
 evaluate budget (depth ::ᵥ branching ::ᵥ nil) = OriginalHereditaryWorkBound.budget branching depth := by
 induction depth with
 | zero =>
   change evaluate (OriginalRawSyntaxTransport.constant 1 1) (branching ::ᵥ nil) = 1
   exact constantEvaluation _ _ _
 | succ depth ih =>
   rw [show budget = Program.recursion (OriginalRawSyntaxTransport.constant 1 1) budgetStep from rfl,
     Proof.recursionSuccessor]
   change evaluate budgetStep (depth ::ᵥ evaluate budget (depth ::ᵥ branching ::ᵥ nil) ::ᵥ branching ::ᵥ nil) = _
   rw [ih,budgetStepEvaluation]
   rfl

theorem unaryComposition {n : Nat} (P : Program 1) (Q : Program n) (v : List.Vector Nat n) :
 evaluate (.composition P (fun _ : Fin 1 => Q)) v = evaluate P (ofFn ![evaluate Q v]) := by
 change evaluate P (ofFn (fun _ : Fin 1 => evaluate Q v)) = evaluate P (ofFn ![evaluate Q v])
 apply congrArg (evaluate P)
 apply congrArg ofFn
 funext i
 have hi : i = 0 := Fin.eq_zero i
 subst i
 rfl

theorem rawJobEvaluation (role typ raw parameter : Nat) :
 evaluate rawJob (ofFn ![Nat.pair role (Nat.pair typ (Nat.pair raw parameter))]) = Nat.pair raw parameter := by
 simp only [rawJob,rightOfEvaluation,evaluate,get_ofFn,Matrix.cons_val_zero,Nat.unpair_pair]

theorem nodesEvaluation (n role typ c : Nat) (s : OriginalHereditaryWorkBound.State (Fin n)) :
 evaluate nodes (ofFn ![OriginalHereditaryAnnotatedExpansion.jobNumber role typ
   (OriginalHereditaryExpansion.jobNumber c s)]) = OriginalStructuralNodeSize.nodeCount s.code := by
 rw [nodes,unaryComposition,leftOfEvaluation]
 unfold OriginalHereditaryAnnotatedExpansion.jobNumber OriginalHereditaryExpansion.jobNumber
 rw [rawJobEvaluation,Nat.unpair_pair]
 exact OriginalStructuralNodeSizeCodeProof.codeCalibration n s.code

theorem contextEvaluation (n role typ c : Nat) (s : OriginalHereditaryWorkBound.State (Fin n)) :
 evaluate contextLength (ofFn ![OriginalHereditaryAnnotatedExpansion.jobNumber role typ
   (OriginalHereditaryExpansion.jobNumber c s)]) = s.context.length := by
 rw [contextLength,unaryComposition,rightOfEvaluation,rightOfEvaluation]
 unfold OriginalHereditaryAnnotatedExpansion.jobNumber OriginalHereditaryExpansion.jobNumber
 rw [rawJobEvaluation,Nat.unpair_pair,Nat.unpair_pair]
 exact OriginalContextInsertionCalibrationProof.lengthContext s.context

attribute [local irreducible] nodes contextLength rawJob

theorem weightEvaluation (n role typ c : Nat) (s : OriginalHereditaryWorkBound.State (Fin n)) :
 evaluate weight (ofFn ![OriginalHereditaryAnnotatedExpansion.jobNumber role typ
 (OriginalHereditaryExpansion.jobNumber c s)]) = OriginalHereditaryWorkBound.weight s := by
 simp only [weight,evaluate,vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one,
 constantEvaluation,addEvaluation,mulEvaluation,nodesEvaluation,contextEvaluation]
 rfl

theorem nativeCalibration : OriginalHereditaryFuelProgramTargets.NativeCalibration := by
 intro n role typ c s
 simp only [fuel,evaluate,vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one,
   constantEvaluation,mulEvaluation,budgetEvaluation,branching,
   succOfEvaluation,weightEvaluation]

theorem runtimeCalibration : OriginalHereditaryFuelProgramTargets.RuntimeCalibration := by
 intro n c a
 exact nativeCalibration n a.role a.typ c a.core

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFuelProgramProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFuelProgramProof
