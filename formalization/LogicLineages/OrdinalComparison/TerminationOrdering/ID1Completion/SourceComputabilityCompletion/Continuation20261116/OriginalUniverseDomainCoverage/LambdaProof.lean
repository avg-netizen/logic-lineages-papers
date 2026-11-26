module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.MemberProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LambdaQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceUnaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.LambdaProof
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
open OriginalLambdaConstructorGraphSyntaxProof (andLeft andRight)

theorem internalLambdaDomain : Targets.InternalLambdaDomain := by
  intro n H W body alpha Delta raw domain child typ gamma context types hc ha ht
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases
    OriginalTypedEnumerationDepthBound.LambdaQueryProof.queries ![domain,child,typ,gamma] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![domain,child,typ,gamma] i).relabel j) =
      ![domain.relabel j,child.relabel j,typ.relabel j,gamma.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  obtain ⟨hpayload,hext,hfields⟩ := OriginalTypedEnumerationDepthBound.LambdaQueryProof.recover
    (domain.relabel j) (child.relabel j) (typ.relabel j) (gamma.relabel j) ys hq
  simp only [graph2Rename,numeralRename]
  have hcj := renameInto hc j Theta hj
  have haj := renameInto ha j Theta hj
  have htj := renameInto ht j Theta hj
  rw [graph2Rename] at hcj
  rw [termAcceptedRename] at haj
  rw [graph1Rename] at htj
  have hpair := OriginalTypedEnumerationDepthBound.PayloadProof.lambdaCode
    (raw.relabel j) (domain.relabel j) (child.relabel j) (ys 0) hcj hpayload
  have hi := OriginalUniverseDecoderInternalAcceptanceUnaryProof.lambdaIff H (member n) W
    (raw.relabel j) (ys 0) (domain.relabel j) (child.relabel j) (typ.relabel j)
    (ys 2) (ys 3) (gamma.relabel j) (ys 1) (context.relabel j) hpair hpayload hfields hext
  have parts := Derivation.implicationElimination (Classical.choice (andLeft hi)) (Classical.choice haj)
  exact MemberProof.membership n (domain.relabel j) (context.relabel j) (types.relabel j)
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight parts)⟩ htj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.LambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.LambdaProof
