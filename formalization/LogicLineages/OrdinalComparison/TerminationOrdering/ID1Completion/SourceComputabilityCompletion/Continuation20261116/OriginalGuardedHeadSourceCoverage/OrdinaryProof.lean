module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.SourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.OrdinaryQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportUnaryAcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.OrdinaryProof
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
open InternalApplicationStepPeelSupportProof (andLeft)
open Continuation20261114.WindowSourceHeadInclusion.ClosureSyntaxProof (closureRename)

theorem internalOrdinaryHead : Targets.InternalOrdinaryHead := by
  intro n arity H body alpha Delta raw head base typ gamma context symbols types hc ha hs ht hclosed
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases
    (OriginalTypedEnumerationDepthBound.OrdinaryQueryProof.queries H) ![head,base] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![head,base] i).relabel j) = ![head.relabel j,base.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  obtain ⟨hpayload,hsig,hfields⟩ := OriginalTypedEnumerationDepthBound.OrdinaryQueryProof.recover
    H (head.relabel j) (base.relabel j) ys hq
  simp only [Targets.sourceHead,InternalRecursionGraphStepSyntaxProof.conjunctionRename,graph1Rename,graph3Rename,numeralRename]
  have hcj := renameInto hc j Theta hj
  have haj := renameInto ha j Theta hj
  have hsj := renameInto hs j Theta hj
  have htj := renameInto ht j Theta hj
  have hclosedj := renameInto hclosed j Theta hj
  rw [graph2Rename] at hcj
  rw [termAcceptedRename] at haj
  rw [graph1Rename] at hsj htj
  rw [closureRename] at hclosedj
  have hi := OriginalUniverseDecoderTransportUnaryAcceptanceProof.ordinaryIff H
    (OriginalUniverseDomainCoverage.member n) (window n arity) (raw.relabel j) (head.relabel j)
    (base.relabel j) (ys 1) (ys 2) (ys 3) (typ.relabel j) (gamma.relabel j) (context.relabel j) hcj hsig hfields
  have parts := Derivation.implicationElimination (Classical.choice (andLeft hi)) (Classical.choice haj)
  exact SourceProof.guarded n arity (head.relabel j) (context.relabel j) (symbols.relabel j) (types.relabel j)
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight parts)⟩ hsj htj hclosedj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.OrdinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.OrdinaryProof
