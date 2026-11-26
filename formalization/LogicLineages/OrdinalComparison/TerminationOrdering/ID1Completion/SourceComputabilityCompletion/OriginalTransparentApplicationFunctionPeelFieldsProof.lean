module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionPeelFieldsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionPeelFieldsQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionPeelFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationStepPeel
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsProof
open InternalApplicationStepPeelSupportProof InternalApplicationStepPeelComponentsProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalApplicationStepPeelWitnessProof
open OriginalTransparentApplicationFunctionPeelFieldsQueryProof

theorem actualFields : OriginalTransparentApplicationFunctionPeelFieldsTargets.ActualFields := by
 intro body alpha Delta d e arrow s t a certificate k lifted htag hlift
 apply queryCases witnessQueries
   (Fin.cons d (Fin.cons e (Fin.cons s (Fin.cons t (Fin.cons a (Fin.cons k Fin.elim0)))))) _
 intro beta j ys Theta hj hq
 simp only [conjunctionRename,graph1Rename,sucRelabel,zRelabel]
 have htag' := renameInto htag j Theta hj
 have hlift' := renameInto hlift j Theta hj
 simp only [taggedEdgeRename] at htag'
 simp only [graph4Rename] at hlift'
 simp only [consTermRename,emptyRename] at hq
 exact fieldsFromQueries (d.relabel j) (e.relabel j) (arrow.relabel j)
   (s.relabel j) (t.relabel j) (a.relabel j) (certificate.relabel j) (k.relabel j)
   (lifted.relabel j) ys htag' hlift' hq

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionPeelFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionPeelFieldsProof
