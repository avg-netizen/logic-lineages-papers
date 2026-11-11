module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLeafAcceptanceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderTransport OriginalTypedDecoderTransportConstructorProof
open OriginalTypedDecoderTransportLogicalProof
open OriginalTypedDecoderInternalAcceptanceLeafProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem variableIff (H : Program 1) (raw index typ gamma : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 variableConstructor raw index))) :
    Nonempty (Derivation body Delta
      ((Accepted H false typ raw gamma).iff (OriginalVariableDecoder.graph (numeral 1) typ index gamma))) :=
  closedApply (actualOriginalTypedInternalVariableAcceptance body H alpha raw index typ gamma)
    (variablePair raw index hc)

theorem bottomIff (H : Program 1) (raw payload typ gamma : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 bottomConstructor raw payload))) :
    Nonempty (Derivation body Delta
      ((Accepted H false typ raw gamma).iff (equal payload typ))) :=
  closedApply (actualOriginalTypedInternalBottomAcceptance body H alpha raw payload typ gamma)
    (bottomPair raw payload hc)

theorem nilIff (H : Program 1) (raw typ gamma : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw Fin.elim0))) :
    Nonempty (Derivation body Delta
      ((Accepted H true typ raw gamma).iff
        (equal (numeral 0) (numeral 0) ⊓ equal typ (numeral 0)))) :=
  closedApply (actualOriginalTypedInternalNilAcceptance body H alpha raw (numeral 0) typ gamma)
    (nilPair raw hc)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLeafAcceptanceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLeafAcceptanceProof
