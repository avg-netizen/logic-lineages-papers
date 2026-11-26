module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportLeafAcceptanceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open OriginalTypedDecoderStepSpecification
open OriginalUniverseDecoderTransport OriginalTypedDecoderTransportConstructorProof
open OriginalTypedDecoderTransportLogicalProof
open OriginalUniverseDecoderInternalAcceptanceLeafProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem variableIff (H : Program 1) (M W : Program 2) (raw index typ gamma c : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 variableConstructor raw index))) :
    Nonempty (Derivation body Delta
      ((Accepted H M W false typ raw gamma c).iff (graph2 M (numeral 1) typ c ⊓ OriginalVariableDecoder.graph (numeral 1) typ index gamma))) :=
  closedApply (actualOriginalUniverseInternalVariableAcceptance body H M W alpha raw index typ gamma c)
    (variablePair raw index hc)

theorem bottomIff (H : Program 1) (M W : Program 2) (raw payload typ gamma c : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 bottomConstructor raw payload))) :
    Nonempty (Derivation body Delta
      ((Accepted H M W false typ raw gamma c).iff (graph2 M (numeral 1) typ c ⊓ equal payload typ))) :=
  closedApply (actualOriginalUniverseInternalBottomAcceptance body H M W alpha raw payload typ gamma c)
    (bottomPair raw payload hc)

theorem nilIff (H : Program 1) (M W : Program 2) (raw typ gamma c : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw Fin.elim0))) :
    Nonempty (Derivation body Delta
      ((Accepted H M W true typ raw gamma c).iff
        (equal (numeral 0) (numeral 0) ⊓ equal typ (numeral 0)))) :=
  closedApply (actualOriginalUniverseInternalNilAcceptance body H M W alpha raw (numeral 0) typ gamma c)
    (nilPair raw hc)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportLeafAcceptanceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportLeafAcceptanceProof
