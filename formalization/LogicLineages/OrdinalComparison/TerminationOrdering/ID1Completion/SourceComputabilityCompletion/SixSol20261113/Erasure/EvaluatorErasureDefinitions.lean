module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- One internal common output of the unchanged original computed evaluator.
This is not equality of raw syntax or of any selected canonical fold. -/
def sameMatrix {alpha : Type} (R : Program 2) (left right parameter : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
 graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) (.var (.inr 0))
   (left.relabel Sum.inl) (parameter.relabel Sum.inl) ⊓
 graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) (.var (.inr 0))
   (right.relabel Sum.inl) (parameter.relabel Sum.inl)
def SameEvaluator {alpha : Type} (R : Program 2) (left right parameter : OTerm alpha) : Formula alpha :=
 existsOne (sameMatrix R left right parameter)
/-- The stable relation carried through deletion. Both original source tests
remain present at the exact current parameter; no decoded/native relation occurs. -/
def AdmittedPair {alpha : Type} (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right parameter : OTerm alpha) : Formula alpha :=
 graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) left parameter ⊓
 (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) right parameter ⊓
  SameEvaluator R left right parameter)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureDefinitions
