module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.ApplicationPositionalDiagnostic.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.ApplicationPositionalDiagnostic.ComparatorGate
open NumberedLeastCodeRepresentative NumberedMultisetNumeric
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Audited definitional comparator only: this proves no diagnostic conjunct.
Both term-check expressions explicitly retain original H/M/W, raw fuel through
termCheck, empty Gamma, and shared context0. -/
theorem exactOriginalContract : Targets.NativeDiagnostic ↔
  (evaluate (Continuation20261115.OriginalCodeValidityGuard.check 0)
    (List.Vector.ofFn ![codeNumber left]) = 1 ∧
   evaluate (Continuation20261115.OriginalCodeValidityGuard.check 0)
    (List.Vector.ofFn ![codeNumber right]) = 1) ∧
  evaluate (Continuation20261114.OriginalHeadMove.headMove 0 arity)
    (List.Vector.ofFn ![headNumber head, codeNumber base, headNumber head,
      codeNumber target, numbersNumber [], numbersNumber (window.map typeNumber)]) = 1 ∧
  evaluate Continuation20261114.OriginalHeadResult.headResult
    (List.Vector.ofFn ![headNumber head]) = typeNumber ground ∧
  evaluate (OriginalUniverseDecoder.termCheck
    (Continuation20261116.OriginalConcreteHeadSignature.signature 0 arity)
    (OriginalRawSyntaxTransport.constant 2 1) (OriginalRawSyntaxTransport.constant 2 1))
    (List.Vector.ofFn ![typeNumber ground, codeNumber left, numbersNumber [], 0]) = 1 ∧
  evaluate (OriginalUniverseDecoder.termCheck
    (Continuation20261116.OriginalConcreteHeadSignature.signature 0 arity)
    (OriginalRawSyntaxTransport.constant 2 1) (OriginalRawSyntaxTransport.constant 2 1))
    (List.Vector.ofFn ![typeNumber ground, codeNumber right, numbersNumber [], 0]) = 0 := Iff.rfl
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.ApplicationPositionalDiagnostic.ComparatorGate
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.ApplicationPositionalDiagnostic.ComparatorGate
