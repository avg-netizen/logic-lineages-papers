module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.AssemblyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AppendRightProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.PreservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.FilterStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.UnaryRankedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open TwoSol20261113.CalibratedPrimary.Membership
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open OriginalRawSyntaxTransport
open SupportProof ConstructorFoldProof

open AssemblyProof
theorem unary : Targets.InternalUnary := by
  intro body alpha Delta which symbols types out head tau ho hp hm
  apply programCases OriginalSourceHeads.casesRecursors (Fin.cons types Fin.elim0) _
  intro beta j Theta list hj hl
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hl
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hoj := renameInto ho j Theta hj
  have hpj := renameInto hp j Theta hj
  have hmj := renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hoj hpj hmj
  have member := unaryCoverage which (types.relabel j) list (head.relabel j) (tau.relabel j) hl hpj hmj
  have lifted := unaryValue OriginalSourceHeads.casesRecursors (.projection 1) list (types.relabel j)
    (Fin.cons (symbols.relabel j) (Fin.cons (types.relabel j) Fin.elim0)) hl
    (projectionValue 1 (Fin.cons (symbols.relabel j) (Fin.cons (types.relabel j) Fin.elim0)))
  exact casesLift (out.relabel j) list (head.relabel j) (symbols.relabel j) (types.relabel j) lifted member hoj
theorem ranked : Targets.InternalRanked := by
  intro body alpha Delta symbols types out head symbol ho hp hm
  apply programCases OriginalSourceHeads.rankedHeads (Fin.cons symbols Fin.elim0) _
  intro beta j Theta list hj hl
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hl
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hoj := renameInto ho j Theta hj
  have hpj := renameInto hp j Theta hj
  have hmj := renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hoj hpj hmj
  have member := rankedCoverage (symbols.relabel j) list (head.relabel j) (symbol.relabel j) hl hpj hmj
  have lifted := unaryValue OriginalSourceHeads.rankedHeads (.projection 0) list (symbols.relabel j)
    (Fin.cons (symbols.relabel j) (Fin.cons (types.relabel j) Fin.elim0)) hl
    (projectionValue 0 (Fin.cons (symbols.relabel j) (Fin.cons (types.relabel j) Fin.elim0)))
  exact rankedLift (out.relabel j) list (head.relabel j) (symbols.relabel j) (types.relabel j) lifted member hoj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.UnaryRankedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.UnaryRankedProof
