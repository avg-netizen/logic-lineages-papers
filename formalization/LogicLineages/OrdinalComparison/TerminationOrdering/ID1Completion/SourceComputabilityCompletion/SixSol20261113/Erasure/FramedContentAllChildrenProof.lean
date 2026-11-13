module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedChildJobCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentAllChildrenProof
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
attribute [local irreducible] programGraph OriginalHereditaryFuelProgram.weight OriginalHereditaryAnnotatedExpansion.expansion
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem allChildren (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B job weight jobs size : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (BelowContent R H M W c B weight)))
 (hj : Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight weight job)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)))
 : Nonempty (Derivation body Delta (ContentVisitsDefinitions.AllContent R size jobs)) := by
 unfold ContentVisitsDefinitions.AllContent
 apply actualFiniteUniversalIntroduction body alpha 2 Delta
 unfold ContentVisitsDefinitions.allBody
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
 obtain ⟨h⟩ := FramedContentChildProof.lookupContent R H M W (c.relabel Sum.inl) (B.relabel Sum.inl) (job.relabel Sum.inl) (weight.relabel Sum.inl) (jobs.relabel Sum.inl) (size.relabel Sum.inl) index child
   hb' hj' hw' he' hl' (andLeft hh) (andRight hh)
 exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentAllChildrenProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentAllChildrenProof
