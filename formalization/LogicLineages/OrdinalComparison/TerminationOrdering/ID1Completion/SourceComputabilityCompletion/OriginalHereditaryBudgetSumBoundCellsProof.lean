module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumRecurrenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteDropProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphExtensionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundCellsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (congSuc)
open InternalOriginalOrderSyntaxProof
open InternalSquareRootArithmeticSupportProof (orderRight)
open InternalListCodecSupportProof (consGraph consGraphRename)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalHereditaryBudgetSumBound OriginalHereditaryBudgetSumBoundSyntaxProof
open InternalClosedPrograms
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroBound (count : OTerm alpha) : Nonempty (Derivation body Delta (Below z (suc count))) := by
 obtain ⟨h⟩ := InternalUnpairArithmeticProof.leftWeakAdd (body := body) (Gamma := Delta) z count
 exact ⟨orderRight z (congSuc (InternalAdditionLawsProof.leftZero count)) h⟩

theorem headBound (count jobs head tail branching cap value : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (consGraph jobs head tail)))
 (hb : Nonempty (Derivation body Delta (CellsBound (suc count) jobs branching cap)))
 (hv : Nonempty (Derivation body Delta (graph2 OriginalHereditaryBudgetSum.jobBudget value head branching))) :
 Nonempty (Derivation body Delta (ltF value (suc cap))) :=
 cellsApply (suc count) jobs branching cap z head value hb
   (InternalApplicationStepPeelSupportProof.andIntro (zeroBound count) (InternalApplicationStepPeelSupportProof.andIntro (OriginalAllPositionContextDeleteBaseProof.lookupZero jobs head tail hc) hv))

theorem tailAt (count jobs head tail branching cap index child value : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (consGraph jobs head tail)))
 (hb : Nonempty (Derivation body Delta (CellsBound (suc count) jobs branching cap)))
 (hf : Nonempty (Derivation body Delta (cellFields count tail branching index child value))) :
 Nonempty (Derivation body Delta (ltF value (suc cap))) := by
 obtain ⟨he⟩ := OriginalAllPositionContextDeleteDropProof.lookupConsIff jobs head tail index child hc
 obtain ⟨hl⟩ := InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight hf)
 have hlookup := Nonempty.intro (Derivation.implicationElimination (Derivation.conjunctionRight he) hl)
 exact cellsApply (suc count) jobs branching cap (suc index) child value hb
   (InternalApplicationStepPeelSupportProof.andIntro (InternalRecursionGraphExtensionSupportProof.successorOrder index count (InternalApplicationStepPeelSupportProof.andLeft hf))
     (InternalApplicationStepPeelSupportProof.andIntro hlookup (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hf))))

theorem tailBound (count jobs head tail branching cap : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (consGraph jobs head tail)))
 (hb : Nonempty (Derivation body Delta (CellsBound (suc count) jobs branching cap))) :
 Nonempty (Derivation body Delta (CellsBound count tail branching cap)) := by
 unfold CellsBound
 apply InternalClosedProgramsBindingProof.actualFiniteUniversalIntroduction body alpha 3 Delta
 let index : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
 let child : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
 let value : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
 let A := cellFields (count.relabel Sum.inl) (tail.relabel Sum.inl) (branching.relabel Sum.inl) index child value
 let Theta := A :: Delta.map (fun f => f.relabel (Sum.inl : alpha → alpha ⊕ Fin 3))
 have inc : ∀ f ∈ Delta, f.relabel (Sum.inl : alpha → alpha ⊕ Fin 3) ∈ Theta := by
   intro f hf
   exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
 have hc' := renameInto hc Sum.inl Theta inc
 rw [consGraphRename] at hc'
 have hb' := renameInto hb Sum.inl Theta inc
 simp only [cellsRename,sucRelabel] at hb'
 obtain ⟨h⟩ := tailAt (count.relabel Sum.inl) (jobs.relabel Sum.inl) (head.relabel Sum.inl)
   (tail.relabel Sum.inl) (branching.relabel Sum.inl) (cap.relabel Sum.inl) index child value
   hc' hb' ⟨Derivation.hypothesis List.mem_cons_self⟩
 exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundCellsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundCellsProof
