module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowStructuralProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsAllProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalTagArithmeticSyntaxProof (z suc sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ContentVisitsDefinitions ContentVisitsSyntax
open OriginalContextInsertion
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem headContent (R : Program 2) (size jobs head tail : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (AllContent R (suc size) jobs)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode jobs head tail))) :
 Nonempty (Derivation body Delta (FramedContentDefinitions.AllFramedContent R head)) :=
 allApply R (suc size) jobs z head ha
   (andIntro (OriginalHereditaryBudgetSumBoundCellsProof.zeroBound size)
     (OriginalAllPositionContextDeleteBaseProof.lookupZero jobs head tail hc))

theorem tailContent (R : Program 2) (size jobs head tail : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (AllContent R (suc size) jobs)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode jobs head tail))) :
 Nonempty (Derivation body Delta (AllContent R size tail)) := by
 unfold AllContent
 apply actualFiniteUniversalIntroduction body alpha 2 Delta
 unfold allBody
 let index : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
 let job : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
 let A := Below index (size.relabel Sum.inl) ⊓ graph2 InternalRawListRecursion.lookup job index (tail.relabel Sum.inl)
 let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 2))
 have hinc : ∀ p ∈ Delta, p.relabel (Sum.inl : alpha → alpha ⊕ Fin 2) ∈ Theta := by
   intro p hp
   exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
 have ha' := renameInto ha Sum.inl Theta hinc
 have hc' := renameInto hc Sum.inl Theta hinc
 simp only [allRename,sucRelabel,graph2Rename] at ha' hc'
 have hh : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hb := InternalRecursionGraphExtensionSupportProof.successorOrder index (size.relabel Sum.inl) (andLeft hh)
 obtain ⟨hi⟩ := OriginalAllPositionContextDeleteDropProof.lookupConsIff
   (jobs.relabel Sum.inl) (head.relabel Sum.inl) (tail.relabel Sum.inl) index job hc'
 obtain ⟨hv⟩ := andRight hh
 have hlk := Nonempty.intro (Derivation.implicationElimination (Derivation.conjunctionRight hi) hv)
 obtain ⟨h⟩ := allApply R (suc (size.relabel Sum.inl)) (jobs.relabel Sum.inl) (suc index) job ha' (andIntro hb hlk)
 exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsAllProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsAllProof
