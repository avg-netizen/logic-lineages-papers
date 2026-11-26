module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableEraseLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableCancellationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (suc)
open InternalOriginalPairingOrderArithmeticProof (formulaCases withHyp)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalVariableLeafProof
open OriginalRawSyntaxTransportInternalVariableEraseLeafProof

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Local cancellation for a genuine original raw variable. The below branch
is unchanged; the other branch uses k < succ i and the actual predecessor graph.
This is a supporting leaf theorem, not all-raw traversal cancellation. -/
theorem variableLeafCancellation (raw shifted erased d k i : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (hs : Nonempty (Derivation body Delta (graph3 (leaf .shift) shifted d k raw)))
    (he : Nonempty (Derivation body Delta (graph3 (leaf .erase) erased d k shifted))) :
    Nonempty (Derivation body Delta (equal erased raw)) := by
  apply formulaCases (InternalLessThan.strictLess i k)
  · have hl : Nonempty (Derivation body (InternalLessThan.strictLess i k :: Delta)
        (InternalLessThan.strictLess i k)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hshift := shiftLeafForwardAt raw shifted d k i i (withHyp hr _)
      (shiftChoiceBelow raw d k i (withHyp hr _) hl) (withHyp hs _)
    have herase := eraseLeafBelowForward shifted erased d k i hshift hl (withHyp he _)
    simpa only [equalEqn] using valueUnique variableConstructor erased raw
      (Fin.cons i Fin.elim0) herase (withHyp hr _)
  · have hn : Nonempty (Derivation body ((InternalLessThan.strictLess i k).not :: Delta)
        (InternalLessThan.strictLess i k).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hshift := shiftLeafForwardAt raw shifted d k i (suc i) (withHyp hr _)
      (shiftChoiceNotBelow raw d k i (withHyp hr _) hn) (withHyp hs _)
    have hgt := InternalUnpairArithmeticProof.notLessWeak i k hn
    have hp := InternalEqualityTestPredecessorProof.predecessorSuccessor
      (body := body) (Gamma := (InternalLessThan.strictLess i k).not :: Delta) i
    have herase := eraseLeafAboveForwardAt shifted erased d k (suc i) i
      hshift hgt hp (withHyp he _)
    simpa only [equalEqn] using valueUnique variableConstructor erased raw
      (Fin.cons i Fin.elim0) herase (withHyp hr _)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableCancellationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableCancellationProof
