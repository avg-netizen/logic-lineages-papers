module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.MemberProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.RootProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBinaryAcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.ApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open OriginalUniverseDecoderInternalAcceptance
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof (termAcceptedRename)
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open OriginalLambdaConstructorGraphSyntaxProof (andLeft)

theorem internalApplicationDomain : Targets.InternalApplicationDomain := by
  intro n H W body alpha Delta raw domain fn arg typ gamma context types hc ha ht
  apply InternalAcceptanceSupportProof.programCases InternalListCodec.consCode ![domain,typ] _
  intro beta j Theta arrow hj harrow
  have hx : (fun i => (![domain,typ] i).relabel j) = ![domain.relabel j,typ.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at harrow
  simp only [graph2Rename,numeralRename]
  have hcj := renameInto hc j Theta hj
  have haj := renameInto ha j Theta hj
  have htj := renameInto ht j Theta hj
  rw [graph3Rename] at hcj
  rw [termAcceptedRename] at haj
  rw [graph1Rename] at htj
  have hi := OriginalUniverseDecoderTransportBinaryAcceptanceProof.applicationIff H (member n) W
    (raw.relabel j) (domain.relabel j) (fn.relabel j) (arg.relabel j) (typ.relabel j) arrow
    (gamma.relabel j) (context.relabel j) hcj harrow
  have parts := Derivation.implicationElimination (Classical.choice (andLeft hi)) (Classical.choice haj)
  have hm := RootProof.requestedType H (member n) W (domain.relabel j) (arg.relabel j)
    (gamma.relabel j) (context.relabel j)
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight parts)⟩
  exact MemberProof.membership n (domain.relabel j) (context.relabel j) (types.relabel j) hm htj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.ApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.ApplicationProof
