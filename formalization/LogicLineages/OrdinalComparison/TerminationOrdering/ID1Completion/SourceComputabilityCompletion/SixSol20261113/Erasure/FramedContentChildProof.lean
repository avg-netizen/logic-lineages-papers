module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentInductionSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedChildJobCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentChildProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalAcceptanceSupportProof (programCases)
open InternalControlGraphSupportProof (emptyRename)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open OriginalHereditaryInternalAgendaSyntaxProof (jobRename)
open OriginalContextInsertionSyntaxProof (lengthRename)
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open FramedContentInductionDefinitions FramedContentInductionSyntax
open Runtime
attribute [local irreducible] programGraph OriginalHereditaryFuelProgram.weight OriginalHereditaryAnnotatedExpansion.expansion
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem lookupContent (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B job weight jobs size index child : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (BelowContent R H M W c B weight)))
 (hj : Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight weight job)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)))
 (hi : Nonempty (Derivation body Delta (OriginalContextInsertion.Below index size)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup child index jobs))) :
 Nonempty (Derivation body Delta (FramedContentDefinitions.AllFramedContent R child)) := by
 have hchild : Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B child)) := SourceFramedChildJobCasesProof.childAt H M W c B job jobs size index child hj he hl hi hv
 apply programCases OriginalHereditaryFuelProgram.weight (Fin.cons child Fin.elim0) _
 intro beta j Theta childWeight hinc hq
 simp only [consTermRename,emptyRename] at hq
 rw [FramedContentSyntax.allContentRename]
 have hb' := renameInto hb j Theta hinc
 have hj' := renameInto hj j Theta hinc
 have hw' := renameInto hw j Theta hinc
 have he' := renameInto he j Theta hinc
 have hl' := renameInto hl j Theta hinc
 have hi' := renameInto hi j Theta hinc
 have hv' := renameInto hv j Theta hinc
 have hchild' := renameInto hchild j Theta hinc
 simp only [belowRename,jobRename,graph1Rename,graph2Rename,lengthRename,OriginalContextInsertion.Below,orderRename]
   at hb' hj' hw' he' hl' hi' hv' hchild'
 have hlt : Nonempty (Derivation body Theta (ltF childWeight (weight.relabel j))) := SourceFramedChildDecreaseProof.actualLookupDecrease body beta Theta
   (job.relabel j) (jobs.relabel j) (size.relabel j) (index.relabel j) (child.relabel j)
   (weight.relabel j) childWeight he' hl' hi' hv' hw' hq
 exact belowApply R H M W (c.relabel j) (B.relabel j) (weight.relabel j)
   (child.relabel j) childWeight hb' hchild' hq hlt
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentChildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentChildProof
