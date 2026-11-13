module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorFixedPointTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorFibreCountermodel
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- One actual ranked binary head; the native zero head has empty BASE. -/
def arity : Fin 1 → Nat := fun _ => 2
def bottom : AuxTerm (Fin 1) arity [] .ground := .bottom .ground
def zero : AuxTerm (Fin 1) arity [] .ground := .ordinary .zero .nil
def leftBase : AuxArguments (Fin 1) arity [] [.ground,.ground] := .cons bottom (.cons zero .nil)
def rightBase : AuxArguments (Fin 1) arity [] [.ground,.ground] := .cons zero (.cons bottom .nil)
def leftTerm : Packed (Fin 1) arity [] := ⟨.ground,.ordinary (.ranked 0) leftBase⟩
def rightTerm : Packed (Fin 1) arity [] := ⟨.ground,.ordinary (.ranked 0) rightBase⟩
def context : OrdinaryArithmeticQuotient.Context 1 := (([0],[.ground]),fun _ _ => false)
def contextCode : Nat := Encodable.encode context
def parameter : Nat := Nat.pair contextCode (typesNumber [])
def leftCode : Nat := packedNumber leftTerm
def rightCode : Nat := packedNumber rightTerm
/-- Deliberately arbitrary retained Program, NOT a calibrated representative. -/
def representative : Program 2 := .projection 0
def evaluator : Program 2 := OriginalHereditaryEvaluatorDefinitions.evaluator representative
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorFibreCountermodel
