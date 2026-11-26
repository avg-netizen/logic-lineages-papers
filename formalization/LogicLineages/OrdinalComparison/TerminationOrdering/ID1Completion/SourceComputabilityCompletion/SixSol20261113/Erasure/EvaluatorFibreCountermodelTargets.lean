module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorFibreCountermodelDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorFibreCountermodelTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedLeastCodeRepresentative NumberedFiniteUniverse
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorFibreCountermodel
/-- Genuine typed terms and the actual original finite head/type window.
There is no fabricated native-symbol family or malformed head signature. -/
def ActualWindow : Prop :=
 Encodable.decode contextCode = some context ∧
 SubtypeClosed (fun t => t ∈ context.1.2) ∧
 HeadInWindow arity context.1.1 context.1.2 (.ranked 0) ∧
 HeadInWindow arity context.1.1 context.1.2 (.zero : Head (Fin 1)) ∧
 InUniverse context.1.1 context.1.2 leftTerm.2 ∧
 InUniverse context.1.1 context.1.2 rightTerm.2
/-- Real original source Programs are selected with all-vector calibrations;
actual source, context guard, membership and both used head-window tests accept.
No source acceptance is a premise of this existential witness. -/
def ActualSource : Prop := ∃ (H G : Program 1) (M W : Program 2),
 OriginalTypedDecoder.HeadSignatureCalibrated 1 arity H ∧
 OriginalTypedDecoder.ContextGuardCalibrated 1 G ∧
 OriginalUniverseDecoder.ContextMemberCalibrated 1 M ∧
 OriginalUniverseDecoder.HeadWindowCalibrated 1 arity W ∧
 evaluate G (List.Vector.ofFn ![contextCode]) = 1 ∧
 evaluate M (List.Vector.ofFn ![typeNumber .ground,contextCode]) = 1 ∧
 evaluate W (List.Vector.ofFn ![headNumber (.ranked (0 : Fin 1)),contextCode]) = 1 ∧
 evaluate W (List.Vector.ofFn ![headNumber (.zero : NumberedAuxiliaryCoding.HeadCode (Fin 1)),contextCode]) = 1 ∧
 evaluate (OriginalUniverseDecoder.source H G M W) (List.Vector.ofFn ![leftCode,parameter]) = 1 ∧
 evaluate (OriginalUniverseDecoder.source H G M W) (List.Vector.ofFn ![rightCode,parameter]) = 1
/-- ACTUAL full computed evaluator collision, including its deletion rows,
while the same explicit arbitrary R distinguishes the ordered packed inputs.
This refutes only overgeneral arbitrary-R compatibility, not calibrated-R
exactness, the paper, canonical preservation, or any existing accepted theorem.
Proof must use checked typed evaluator calibration/fixedPoint and true empty
rows; no native_decide or enormous raw-loop evaluation shortcut. -/
def ActualCollision : Prop :=
 evaluate (OriginalHereditaryDeletionRows.rows evaluator) (List.Vector.ofFn ![leftCode,parameter]) = 0 ∧
 evaluate (OriginalHereditaryDeletionRows.rows evaluator) (List.Vector.ofFn ![rightCode,parameter]) = 0 ∧
 evaluate evaluator (List.Vector.ofFn ![leftCode,parameter]) =
   evaluate evaluator (List.Vector.ofFn ![rightCode,parameter]) ∧
 evaluate representative (List.Vector.ofFn ![leftCode,parameter]) ≠
   evaluate representative (List.Vector.ofFn ![rightCode,parameter])
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorFibreCountermodelTargets
