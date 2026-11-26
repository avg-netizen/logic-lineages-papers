module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.UnarySupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.UnaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open HeadWindowBranchAdequacy (member)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open ClosureSyntaxProof
theorem proof : Targets.InternalUnary := by
  intro n arity body alpha Delta which raw payload symbols types hc hp hw
  have hm := UnarySupportProof.unaryPayload which raw payload symbols types n arity hc hp hw
  apply programCases OriginalSourceHeads.rawWindow (Fin.cons symbols (Fin.cons types Fin.elim0)) _
  intro beta j Theta out hj hr
  simp only [consTermRename,emptyRename] at hr
  have hpj := renameInto hp j Theta hj
  have hwj := renameInto hw j Theta hj
  have hmj := renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,member,GuardedSourceSyntaxProof.numeralRename] at hpj hwj hmj ⊢
  exact SupportProof.sourceFromRaw n arity out (raw.relabel j) (symbols.relabel j) (types.relabel j) hr hwj
    (RawHeadWindowCoverage.UnaryRankedProof.unary body beta Theta which (symbols.relabel j) (types.relabel j)
      out (raw.relabel j) (payload.relabel j) hr hpj hmj)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.UnaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.UnaryProof
