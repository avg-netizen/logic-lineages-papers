module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentLocalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.UnsortedChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationSmallProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open RankArgumentDefinitions ObservationDescentDefinitions
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem baseSmall (kind : UnsortedChildDefinitions.BaseSlot)
 (out base inner root rows payload raw sorted : OTerm alpha)
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out base inner)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner root rows)))
 (hg : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing root (numeral (UnsortedChildDefinitions.tag kind)) payload)))
 (hsel : Nonempty (Derivation body Delta (graph1 (select (listPath (UnsortedChildDefinitions.slot kind))) sorted payload)))
 (hsort : Nonempty (Derivation body Delta (graph1 OriginalNumericListSort.sort sorted raw)))
 : Nonempty (Derivation body Delta (AllSmall raw out)) := by
 unfold AllSmall
 apply actualFiniteUniversalIntroduction body alpha 5 Delta
 let j : alpha → alpha ⊕ Fin 5 := Sum.inl
 let count : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
 let index : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
 let typed : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
 let typ : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
 let child : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
 let A := OriginalContextInsertion.lengthGraph count (raw.relabel j) ⊓
   (OriginalContextInsertion.Below index count ⊓
    (graph2 InternalRawListRecursion.lookup typed index (raw.relabel j) ⊓
     graph2 InternalPairing.pairing typed typ child))
 let Theta := A :: Delta.map (fun f => f.relabel j)
 have inc : ∀ f ∈ Delta, f.relabel j ∈ Theta := fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
 have ho' := renameInto ho j Theta inc
 have hi' := renameInto hi j Theta inc
 have hg' := renameInto hg j Theta inc
 have hsel' := renameInto hsel j Theta inc
 have hsort' := renameInto hsort j Theta inc
 simp only [graph1Rename,graph2Rename,OriginalRawSyntaxTransportInternalParserSyntaxProof.numeralRename,sucRelabel,zRelabel] at ho' hi' hg' hsel' hsort'
 have h : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨result⟩ := UnsortedChildProof.actualUnsortedChildDescent kind body (alpha ⊕ Fin 5) Theta
   (out.relabel j) (base.relabel j) (inner.relabel j) (root.relabel j) (rows.relabel j) (payload.relabel j) (raw.relabel j) (sorted.relabel j) count index typed typ child
   ho' hi' hg' hsel' hsort' (andLeft h) (andLeft (andRight h))
   (andLeft (andRight (andRight h))) (andRight (andRight (andRight h)))
 exact ⟨Derivation.implicationIntroduction result⟩

theorem storedSmall (slot : ListSlot)
 (out base inner root rows payload raw label : OTerm alpha)
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out base inner)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner root rows)))
 (hg : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing root label payload)))
 (hsel : Nonempty (Derivation body Delta (graph1 (select (listPath slot)) raw payload)))
 : Nonempty (Derivation body Delta (AllSmall raw out)) := by
 unfold AllSmall
 apply actualFiniteUniversalIntroduction body alpha 5 Delta
 let j : alpha → alpha ⊕ Fin 5 := Sum.inl
 let count : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
 let index : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
 let typed : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
 let typ : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
 let child : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
 let A := OriginalContextInsertion.lengthGraph count (raw.relabel j) ⊓
   (OriginalContextInsertion.Below index count ⊓
    (graph2 InternalRawListRecursion.lookup typed index (raw.relabel j) ⊓
     graph2 InternalPairing.pairing typed typ child))
 let Theta := A :: Delta.map (fun f => f.relabel j)
 have inc : ∀ f ∈ Delta, f.relabel j ∈ Theta := fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
 have ho' := renameInto ho j Theta inc
 have hi' := renameInto hi j Theta inc
 have hg' := renameInto hg j Theta inc
 have hsel' := renameInto hsel j Theta inc
 simp only [graph1Rename,graph2Rename,OriginalRawSyntaxTransportInternalParserSyntaxProof.numeralRename,sucRelabel,zRelabel] at ho' hi' hg' hsel'
 have h : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨result⟩ := ObservationDescentProof.actualStoredChildDescent slot body (alpha ⊕ Fin 5) Theta
   (out.relabel j) (base.relabel j) (inner.relabel j) (root.relabel j) (rows.relabel j) (label.relabel j) (payload.relabel j) (raw.relabel j) count index typed typ child
   ho' hi' hg' hsel' (andLeft h) (andLeft (andRight h))
   (andLeft (andRight (andRight h))) (andRight (andRight (andRight h)))
 exact ⟨Derivation.implicationIntroduction result⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationSmallProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationSmallProof
