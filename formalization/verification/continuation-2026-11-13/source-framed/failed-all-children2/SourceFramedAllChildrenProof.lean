module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedChildJobCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedAllChildrenProof
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
open InternalOriginalOrderSyntaxProof (orderRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SourceFramedDefinitions SourceFramedSyntax
attribute [local irreducible] programGraph OriginalHereditaryFuelProgram.weight OriginalHereditaryAnnotatedExpansion.expansion
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem lookupComplete (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B job weight jobs size index child : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (BelowCompletion R H M W c B weight)))
 (hj : Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight weight job)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)))
 (hi : Nonempty (Derivation body Delta (OriginalContextInsertion.Below index size)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup child index jobs))) :
 Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Completion R child)) := by
 have hchild : Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B child)) := SourceFramedChildJobCasesProof.childAt H M W c B job jobs size index child hj he hl hi hv
 apply programCases OriginalHereditaryFuelProgram.weight (Fin.cons child Fin.elim0) _
 intro beta j Theta childWeight hinc hq
 simp only [consTermRename,emptyRename] at hq
 rw [JobCompletionSyntax.completionRename]
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
theorem allChildren (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B job weight jobs size : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (BelowCompletion R H M W c B weight)))
 (hj : Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight weight job)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)))
 : Nonempty (Derivation body Delta (VisitListCompletionDefinitions.AllComplete R size jobs)) := by
 unfold VisitListCompletionDefinitions.AllComplete
 apply actualFiniteUniversalIntroduction body alpha 2 Delta
 unfold VisitListCompletionDefinitions.allBody
 let index : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
 let child : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
 let A := OriginalContextInsertion.Below index (size.relabel Sum.inl) ⊓
   graph2 InternalRawListRecursion.lookup child index (jobs.relabel Sum.inl)
 let Theta := A :: Delta.map (fun f => f.relabel (Sum.inl : alpha → alpha ⊕ Fin 2))
 have hinc : ∀ f ∈ Delta, f.relabel (Sum.inl : alpha → alpha ⊕ Fin 2) ∈ Theta :=
   fun f h => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,h,rfl⟩)
 have hh : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hb' := renameInto hb Sum.inl Theta hinc
 have hj' := renameInto hj Sum.inl Theta hinc
 have hw' := renameInto hw Sum.inl Theta hinc
 have he' := renameInto he Sum.inl Theta hinc
 have hl' := renameInto hl Sum.inl Theta hinc
 simp only [belowRename,jobRename,graph1Rename,lengthRename] at hb' hj' hw' he' hl'
 obtain ⟨h⟩ := lookupComplete R H M W (c.relabel Sum.inl) (B.relabel Sum.inl) (job.relabel Sum.inl) (weight.relabel Sum.inl) (jobs.relabel Sum.inl) (size.relabel Sum.inl) index child
   hb' hj' hw' he' hl' (andLeft hh) (andRight hh)
 exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedAllChildrenProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedAllChildrenProof
