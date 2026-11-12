module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorBoundsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalPayloadArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalBoundProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorSelectorBoundsProof
open OriginalLambdaTraversalInternalPayloadArithmeticProof
open InternalApplicationStepPeelSupportProof (andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Literal tag7 raw-spine tail strictly decreases in the original calculus.
This does not identify the tagged spine with numeric-list encoding. -/
theorem rawTailBound (raw typ child tail : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ child tail))) :
 Nonempty (Derivation body Delta (InternalLessThan.strictLess tail raw)) := by
 let xs : Fin 1 → OTerm alpha := ![raw]
 have ht := consTag (.projection 0) raw typ child tail xs (projectionValue 0 xs) hc
 have hf := consHead (.projection 0) raw typ child tail xs (projectionValue 0 xs) hc
 have hs := consTail (.projection 0) raw typ child tail xs (projectionValue 0 xs) hc
 have htag := unaryRecover InternalUnpair.left (.projection 0) (numeral 7) raw xs ht (projectionValue 0 xs)
 have hb := binarySelectorsBound 7 (by decide) raw child tail htag hf hs
 exact andRight (applicationDescent raw child tail hb)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalBoundProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalBoundProof
