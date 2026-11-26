module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorOpenCoreProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalCoverNumberedLayerOpenDataProof (quintInputsRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverArgumentCellsTargets (axisInclusion)
open NumberedWindowInternalCoverArgumentCellsTransportProof (axisRename)
open NumberedWindowInternalCoverSelectedSuccessorTargets

attribute [local irreducible] programGraph

theorem tapeRename {α β : Type} (H K ids ts args : OTerm α) (j : α → β) :
    (fun i => (stepTape H K ids ts args i).relabel j) =
      stepTape (H.relabel j) (K.relabel j) (ids.relabel j) (ts.relabel j) (args.relabel j) :=
  quintInputsRename H K ids ts args j

theorem reportRename {α β : Type} (P : Program 5) (out H K ids ts args : OTerm α) (j : α → β) :
    (stepReport P out H K ids ts args).relabel j =
      stepReport P (out.relabel j) (H.relabel j) (K.relabel j) (ids.relabel j) (ts.relabel j) (args.relabel j) := by
  simp only [stepReport,programRename,tapeRename]

def OpenPartInclusionAtKey (P : Program 5) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (old next H K ids ids' ts ts' args args' key : OTerm α),
  Nonempty (Derivation body Γ (stepReport P old H K ids ts args)) →
  Nonempty (Derivation body Γ (stepReport P next H K ids' ts' args')) →
  Nonempty (Derivation body Γ (axisInclusion ids ids')) →
  Nonempty (Derivation body Γ (axisInclusion ts ts')) →
  Nonempty (Derivation body Γ (axisInclusion args args')) →
  Nonempty (Derivation body Γ (memberGraph old key)) →
  Nonempty (Derivation body Γ (memberGraph next key))

theorem includeOfAtKey (P : Program 5) (atKey : OpenPartInclusionAtKey P) : OpenPartInclusion P := by
  intro body α Γ old next H K ids ids' ts ts' args args' small large hi ht ha
  let j : α → α ⊕ Fin 1 := Sum.inl
  let key : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let M := memberGraph (old.relabel j) key
  let Δ := M :: Γ.map (fun q => q.relabel j)
  have keep : ∀ p ∈ Γ, p.relabel j ∈ Δ := by
    intro p h
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,h,rfl⟩)
  have small' := renameInto small j Δ keep
  have large' := renameInto large j Δ keep
  rw [reportRename] at small' large'
  have hi' := renameInto hi j Δ keep
  have ht' := renameInto ht j Δ keep
  have ha' := renameInto ha j Δ keep
  rw [axisRename] at hi' ht' ha'
  obtain ⟨result⟩ := atKey body (α ⊕ Fin 1) Δ (old.relabel j) (next.relabel j)
    (H.relabel j) (K.relabel j) (ids.relabel j) (ids'.relabel j) (ts.relabel j) (ts'.relabel j)
    (args.relabel j) (args'.relabel j) key small' large' hi' ht' ha'
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction result)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorOpenCoreProof
