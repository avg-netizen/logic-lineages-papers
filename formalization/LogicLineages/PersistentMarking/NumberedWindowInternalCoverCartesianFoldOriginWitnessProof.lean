module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldOriginSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldOriginWitnessProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb suc z)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (headMember tailMember)
open NumberedWindowInternalCoverCartesianFoldOriginTargets
open NumberedWindowInternalCoverCartesianFoldOriginSyntaxProof (originInstance originRename)

attribute [local irreducible] programGraph
variable {k : Nat} {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem blockValue (D : Program (k+1)) (source image block : OTerm α)
    (params : Fin k → OTerm α)
    (run : Nonempty (Derivation body Γ (programGraph D block (Fin.cons source params)))) :
    Nonempty (Derivation body Γ
      (programGraph (blockCall D) block (Fin.cons source (Fin.cons image params)))) := by
  let xs : Fin (k+2) → OTerm α := Fin.cons source (Fin.cons image params)
  apply compositionValue D blockSelectors block xs (Fin.cons source params) run
  intro i
  exact Fin.cases (projectionValue 0 xs) (fun j => projectionValue j.succ.succ xs) i

theorem hitOfBlockMember (D : Program (k+1)) (source image block : OTerm α)
    (params : Fin k → OTerm α)
    (run : Nonempty (Derivation body Γ (programGraph D block (Fin.cons source params))))
    (hit : Nonempty (Derivation body Γ (memberGraph block image))) :
    Nonempty (Derivation body Γ (blockHit D source image params)) := by
  let xs : Fin (k+2) → OTerm α := Fin.cons source (Fin.cons image params)
  apply compositionValue scratchMember ![blockCall D,.projection 1] (suc z) xs ![block,image] hit
  intro i
  exact Fin.cases (blockValue D source image block params run)
    (Fin.cases (projectionValue 1 xs) (fun j => Fin.elim0 j)) i

theorem blockMemberOfHit (D : Program (k+1)) (source image block : OTerm α)
    (params : Fin k → OTerm α)
    (run : Nonempty (Derivation body Γ (programGraph D block (Fin.cons source params))))
    (hit : Nonempty (Derivation body Γ (blockHit D source image params))) :
    Nonempty (Derivation body Γ (memberGraph block image)) := by
  let xs : Fin (k+2) → OTerm α := Fin.cons source (Fin.cons image params)
  apply compositionRecover scratchMember ![blockCall D,.projection 1] (suc z) xs ![block,image] hit
  intro i
  exact Fin.cases (blockValue D source image block params run)
    (Fin.cases (projectionValue 1 xs) (fun j => Fin.elim0 j)) i

private theorem introduce (D : Program (k+1)) (raw source image : OTerm α) (params : Fin k → OTerm α)
    (sourceIn : Nonempty (Derivation body Γ (memberGraph raw source)))
    (imageIn : Nonempty (Derivation body Γ (blockHit D source image params))) :
    Nonempty (Derivation body Γ (hasOrigin D raw image params)) := by
  obtain ⟨sourceIn⟩ := sourceIn
  obtain ⟨imageIn⟩ := imageIn
  unfold hasOrigin
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb source)
  rw [originInstance]
  exact Derivation.conjunctionIntroduction sourceIn imageIn

theorem atHead (D : Program (k+1)) (raw head tail image : OTerm α) (params : Fin k → OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph raw head tail)))
    (hit : Nonempty (Derivation body Γ (blockHit D head image params))) :
    Nonempty (Derivation body Γ (hasOrigin D raw image params)) :=
  introduce D raw head image params (headMember raw head tail head cell ⟨refl head⟩) hit

theorem fromTail (D : Program (k+1)) (raw head tail image : OTerm α) (params : Fin k → OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph raw head tail)))
    (old : Nonempty (Derivation body Γ (hasOrigin D tail image params))) :
    Nonempty (Derivation body Γ (hasOrigin D raw image params)) := by
  obtain ⟨old⟩ := old
  unfold hasOrigin at old
  let A := originBinder D tail image params
  let Δ := A :: Γ.map weaken
  let j : α → α ⊕ Fin 1 := Sum.inl
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let p : Fin k → OTerm (α ⊕ Fin 1) := fun i => (params i).relabel j
  have keep : ∀ q ∈ Γ, q.relabel j ∈ Δ := by
    intro q h
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,h,rfl⟩)
  have hc := renameInto cell j Δ keep
  rw [consGraphRename] at hc
  have row : Derivation body Δ (originRow D (tail.relabel j) w (image.relabel j) p) :=
    Derivation.hypothesis List.mem_cons_self
  have newSource := tailMember (raw.relabel j) (head.relabel j) (tail.relabel j) w hc
    ⟨Derivation.conjunctionLeft row⟩
  have found := introduce D (raw.relabel j) w (image.relabel j) p newSource
    ⟨Derivation.conjunctionRight row⟩
  rw [← originRename D raw image params j] at found
  obtain ⟨found⟩ := found
  exact ⟨Derivation.existentialElimination old found⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldOriginWitnessProof
