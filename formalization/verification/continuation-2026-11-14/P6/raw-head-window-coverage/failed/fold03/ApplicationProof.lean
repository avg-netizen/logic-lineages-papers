module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.ApplicationFoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.AssemblyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.RelationFoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AppendRightProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.PreservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.FilterStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.ApplicationProof
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

open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open SupportProof FoldCoreProof

open ConstructorFoldProof

open ApplicationFoldProof AssemblyProof

theorem applicationsCoverage (types sigma tau image payload out : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph1 OriginalSourceHeads.applications out types)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload sigma tau)))
    (hh : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing image (numeral 4) payload)))
    (hms : Nonempty (Derivation body Delta (graph2 contains (numeral 1) types sigma)))
    (hmt : Nonempty (Derivation body Delta (graph2 contains (numeral 1) types tau))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out image)) := by
  apply programCases OriginalSourceHeads.appRow (Fin.cons types (Fin.cons sigma Fin.elim0)) _
  intro beta j Theta row hj hr
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hr
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hfj := renameInto hf j Theta hj
  have hpj := renameInto hp j Theta hj
  have hhj := renameInto hh j Theta hj
  have hmsj := renameInto hms j Theta hj
  have hmtj := renameInto hmt j Theta hj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hfj hpj hhj hmsj hmtj
  have hm := rowCoverage (types.relabel j) (sigma.relabel j) (tau.relabel j) (image.relabel j)
    (payload.relabel j) row hr hpj hhj hmtj
  let xs : Fin 3 → OTerm beta := Fin.cons (image.relabel j) (Fin.cons (sigma.relabel j) (Fin.cons (types.relabel j) Fin.elim0))
  have hrow := binaryValue OriginalSourceHeads.appRow (.projection 2) (.projection 1) row
    (types.relabel j) (sigma.relabel j) xs hr (projectionValue 2 xs) (projectionValue 1 xs)
  have ht : Nonempty (Derivation body Theta (programGraph rowMember (numeral 1) xs)) :=
    binaryValue contains (.composition OriginalSourceHeads.appRow ![.projection 2,.projection 1]) (.projection 0)
      (numeral 1) row (image.relabel j) xs hm hrow (projectionValue 0 xs)
  have hfold := binaryRecover (InternalRawListRecursion.listRec (constant 1 0) OriginalSourceHeads.appsStep)
    (.projection 0) (.projection 0) (out.relabel j) (types.relabel j) (types.relabel j)
    (Fin.cons (types.relabel j) Fin.elim0) hfj
    (projectionValue 0 (Fin.cons (types.relabel j) Fin.elim0)) (projectionValue 0 (Fin.cons (types.relabel j) Fin.elim0))
  exact RelationFoldProof.coverage (constant 1 0) OriginalSourceHeads.appsStep rowMember outerHit outerTail
    (types.relabel j) (sigma.relabel j) (image.relabel j) (out.relabel j)
    (Fin.cons (types.relabel j) Fin.elim0) ht hmsj hfold

theorem application : Targets.InternalApplication := by
  intro body alpha Delta symbols types out head payload sigma tau ho hp hh hms hmt
  apply programCases OriginalSourceHeads.applications (Fin.cons types Fin.elim0) _
  intro beta j Theta list hj hl
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hl
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hoj := renameInto ho j Theta hj
  have hpj := renameInto hp j Theta hj
  have hhj := renameInto hh j Theta hj
  have hmsj := renameInto hms j Theta hj
  have hmtj := renameInto hmt j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hoj hpj hhj hmsj hmtj
  have member := applicationsCoverage (types.relabel j) (sigma.relabel j) (tau.relabel j) (head.relabel j)
    (payload.relabel j) list hl hpj hhj hmsj hmtj
  have lifted := unaryValue OriginalSourceHeads.applications (.projection 1) list (types.relabel j)
    (Fin.cons (symbols.relabel j) (Fin.cons (types.relabel j) Fin.elim0)) hl
    (projectionValue 1 (Fin.cons (symbols.relabel j) (Fin.cons (types.relabel j) Fin.elim0)))
  exact applicationLift (out.relabel j) list (head.relabel j) (symbols.relabel j) (types.relabel j) lifted member hoj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.ApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.ApplicationProof
