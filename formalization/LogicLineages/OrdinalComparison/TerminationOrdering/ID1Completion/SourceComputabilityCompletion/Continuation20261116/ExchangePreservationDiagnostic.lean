module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCodeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.ExchangePreservationDiagnostic
open Source Source.SourceMarkedSyntax NumberedAuxiliaryCoding NumberedFiniteUniverse
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Diagnostic only, not a counted packet. All native heads are available at n=0. -/
def arity : Fin 0 → Nat := Fin.elim0
def types : List Ty := [.ground,.arrow .ground .ground]
def leftCode : Code (Fin 0) := .numbered 0 .zero .ground .argumentsNil [] .argumentsNil
def rightCode : Code (Fin 0) := .numbered 0 .succ .ground .argumentsNil [] .argumentsNil
/-- Deliberately uncalibrated permitted H: zero head gets signature (ground,[]),
succ head gets rejection. This is precisely the arbitrary-H boundary. -/
def H : Program 1 := InternalAcceptance.branch (.projection 0)
  (OriginalRawSyntaxTransport.constant 1 1) (OriginalRawSyntaxTransport.constant 1 0)
theorem headsEquivalent : RecursiveComparison.headEquivalent
    (.zero : Head (Fin 0)) .succ := rfl
theorem zeroInWindow : HeadInWindow arity [] types .zero := by decide
theorem succInWindow : HeadInWindow arity [] types .succ := by decide
theorem basesPermute : NumberedExchangeCode.argumentPermutation
    (.argumentsNil : Code (Fin 0)) .argumentsNil = true := by decide
theorem actualExchange : NumberedExchangeCode.codeExchange arity [] types leftCode rightCode = true := by decide
theorem explicitTypeEqual : (.ground : Ty) = .ground := rfl
theorem zeroSignature : evaluate H (List.Vector.ofFn (fun _ : Fin 1 =>
    NumberedLeastCodeRepresentative.headNumber (.zero : HeadCode (Fin 0)))) = 1 := by rfl
theorem succSignature : evaluate H (List.Vector.ofFn (fun _ : Fin 1 =>
    NumberedLeastCodeRepresentative.headNumber (.succ : HeadCode (Fin 0)))) = 0 := by rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.ExchangePreservationDiagnostic
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.ExchangePreservationDiagnostic
