module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedHeadMoveReflexivity.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedHeadMoveReflexivity.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open OriginalTypedDecoderInternalAcceptance OriginalTypedDecoderInternalAcceptanceSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem permutation : Targets.InternalPermutation := SupportProof.permutation

theorem basic : Targets.InternalBasic := by
  intro n arity body H alpha Delta which raw base symbols types argumentTypes gamma hp hw ha
  exact SupportProof.accept n arity H raw base symbols types argumentTypes gamma hw
    (WindowSourceHeadInclusion.BasicProof.proof n arity body alpha Delta which raw symbols types hp hw) ha

theorem unary : Targets.InternalUnary := by
  intro n arity body H alpha Delta which raw payload base symbols types argumentTypes gamma hc hp hw ha
  exact SupportProof.accept n arity H raw base symbols types argumentTypes gamma hw
    (WindowSourceHeadInclusion.UnaryProof.proof n arity body alpha Delta which raw payload symbols types hc hp hw) ha

theorem application : Targets.InternalApplication := by
  intro n arity body H alpha Delta raw payload sigma tau base symbols types argumentTypes gamma hp hpair hw ha
  exact SupportProof.accept n arity H raw base symbols types argumentTypes gamma hw
    (WindowSourceHeadInclusion.ApplicationProof.proof n arity body alpha Delta raw payload sigma tau symbols types hp hpair hw) ha

theorem ranked : Targets.InternalRanked := by
  intro n arity body H alpha Delta raw symbol base symbols types argumentTypes gamma hp hw ha
  exact SupportProof.accept n arity H raw base symbols types argumentTypes gamma hw
    (WindowSourceHeadInclusion.RankedProof.proof n arity body alpha Delta raw symbol symbols types hp hw) ha

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedHeadMoveReflexivity.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedHeadMoveReflexivity.Proof
