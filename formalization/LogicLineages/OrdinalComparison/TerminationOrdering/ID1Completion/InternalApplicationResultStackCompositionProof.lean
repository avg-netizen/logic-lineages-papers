module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionWorkProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionResultProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationResultStackComposition
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalResultStackTerminalIteration :
    InternalApplicationResultStackCompositionTargets.ActualOriginalResultStackTerminalIteration :=
  InternalApplicationResultStackCompositionBasicProof.actualOriginalResultStackTerminalIteration

theorem actualOriginalResultStackRunZero :
    InternalApplicationResultStackCompositionTargets.ActualOriginalResultStackRunZero :=
  InternalApplicationResultStackCompositionBasicProof.actualOriginalResultStackRunZero

theorem actualOriginalResultStackWorkAppend :
    InternalApplicationResultStackCompositionTargets.ActualOriginalResultStackWorkAppend :=
  InternalApplicationResultStackCompositionWorkProof.actualOriginalResultStackWorkAppend

theorem actualOriginalResultStackResultSuffixFrame :
    InternalApplicationResultStackCompositionTargets.ActualOriginalResultStackResultSuffixFrame :=
  InternalApplicationResultStackCompositionResultProof.actualOriginalResultStackResultSuffixFrame

/-- Contextual consumer of the exact output-preserving work composition. -/
theorem workAppend {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    (guard leaf : Program 1) (combine : Program 4)
    (first second frontWork suffix joined initialResults middleResults finalResults : OrdinaryArithmetic.Term α)
    (ha : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma
      (actualRun guard leaf combine first frontWork initialResults middleResults)))
    (hs : Nonempty (Derivation body Gamma
      (actualRun guard leaf combine second suffix middleResults finalResults))) :
    Nonempty (Derivation body Gamma (actualRun guard leaf combine
      (OrdinaryArithmetic.addTerm first second) joined initialResults finalResults)) :=
  InternalApplicationResultStackCompositionInductionCoreProof.workRowApply guard leaf combine
    first second frontWork suffix joined initialResults middleResults finalResults
    (InternalApplicationResultStackCompositionWorkProof.allRows guard leaf combine first) ha hf hs

/-- Contextual consumer retaining the entire appended result background. -/
theorem resultSuffixFrame {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    (guard leaf : Program 1) (combine : Program 4)
    (count work initialResults finalResults background framedInitial framedFinal : OrdinaryArithmetic.Term α)
    (hr : Nonempty (Derivation body Gamma
      (actualRun guard leaf combine count work initialResults finalResults)))
    (hi : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append framedInitial initialResults background)))
    (hf : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append framedFinal finalResults background))) :
    Nonempty (Derivation body Gamma (actualRun guard leaf combine count work framedInitial framedFinal)) :=
  InternalApplicationResultStackCompositionInductionCoreProof.resultRowApply guard leaf combine
    count work initialResults finalResults background framedInitial framedFinal
    (InternalApplicationResultStackCompositionResultProof.allRows guard leaf combine count) hr hi hf

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionProof
