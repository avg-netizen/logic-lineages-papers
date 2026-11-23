module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryGuardsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryNonemptyProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryOpenProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalDirectSourcePartitionRawTargets
open NumberedWindowInternalDirectSourcePartitionRawProof (exact_OpenRawSourceDecode)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser keepThrough)
open NumberedWindowInternalDirectBoundaryNonemptyProof (exact_OpenRemovedScratchCons)
open NumberedWindowInternalDirectBoundaryGuardsTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem recoverSlot (p : Program 1) (i : Fin 3) (xs : Fin 3 → OTerm α)
    (held : Nonempty (Derivation B Γ (programGraph (atSlot p i) (suc z) xs))) :
    Nonempty (Derivation B Γ (unary p (suc z) (xs i))) := by
  apply compositionRecover p ![.projection i] (suc z) xs ![xs i] held
  intro k
  obtain rfl := Fin.eq_zero k
  exact projectionValue i xs

private theorem decodedGuards (scalar : Program 1) (ds dt dr : OTerm α)
    (ran : Nonempty (Derivation B Γ (programGraph (boundaryScratch scalar) (suc z) (sourceTape ds dt dr)))) :
    Nonempty (Derivation B Γ (unary (typedScratch scalar) (suc z) ds)) ∧
    Nonempty (Derivation B Γ (unary (typedScratch scalar) (suc z) dt)) ∧
    Nonempty (Derivation B Γ (unary presentScratch (suc z) dr)) := by
  let xs := sourceTape ds dt dr
  let p := typedScratch scalar
  obtain ⟨both⟩ := conjunctionRecover (atSlot p 0) (conjunction (atSlot p 1) (atSlot presentScratch 2)) xs ran
  obtain ⟨rest⟩ := conjunctionRecover (atSlot p 1) (atSlot presentScratch 2) xs ⟨Derivation.conjunctionRight both⟩
  exact ⟨recoverSlot p 0 xs ⟨Derivation.conjunctionLeft both⟩,
    recoverSlot p 1 xs ⟨Derivation.conjunctionLeft rest⟩,
    recoverSlot presentScratch 2 xs ⟨Derivation.conjunctionRight rest⟩⟩

theorem exact_OpenRawGuards : ExactOpenRawGuards := by
  intro scalar B α Γ src dst removed goal held next
  apply exact_OpenRawSourceDecode (boundaryScratch scalar) B α Γ src dst removed goal held
  intro β j Δ ds dt dr keep parsed ran
  obtain ⟨asrc,adst,alive⟩ := decodedGuards scalar ds dt dr ran
  apply exact_OpenRemovedScratchCons dr (goal.relabel j) alive
  intro γ k Θ hd tl retain cell
  let g := k ∘ j
  have s := renameParser (src.relabel j) ds parsed.source k Θ retain
  have t := renameParser (dst.relabel j) dt parsed.kept k Θ retain
  have r := renameParser (removed.relabel j) dr parsed.removed k Θ retain
  have s' : Nonempty (Derivation B Θ (unary (typedScratch scalar) (suc z) (ds.relabel k))) := by
    simpa only [unaryRename,sucRelabel,zRelabel] using renameInto asrc k Θ retain
  have t' : Nonempty (Derivation B Θ (unary (typedScratch scalar) (suc z) (dt.relabel k))) := by
    simpa only [unaryRename,sucRelabel,zRelabel] using renameInto adst k Θ retain
  have p : ParsedTriplet B Θ (src.relabel g) (dst.relabel g) (removed.relabel g)
      (ds.relabel k) (dt.relabel k) (dr.relabel k) :=
    ⟨by simpa only [g,Term.relabel_relabel] using s,
     by simpa only [g,Term.relabel_relabel] using t,
     by simpa only [g,Term.relabel_relabel] using r⟩
  rw [formulaRelabelComposition j k goal]
  exact next γ g Θ (ds.relabel k) (dt.relabel k) (dr.relabel k) hd tl
    (keepThrough j k keep retain) ⟨p,s',t',cell⟩

#print axioms exact_OpenRawGuards
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryOpenProof
