module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldImageProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalControlGraphSupportProof (valueUnique programRename)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalListInduction (atCode atIndex constructorBody constructors)
open ID1Completion.InternalListInductionProof (actualOriginalListInductionAtCode)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (consTermRename)
open ID1Completion.InternalRawListRecursionProof (nilRecover)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseScratchMembership (memberBase memberStep)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverCartesianFoldTargets
open NumberedWindowInternalCoverCartesianFoldSyntaxProof
open NumberedWindowInternalCoverCartesianFoldImageProof (imageOfMember memberOfImage)
open NumberedWindowInternalCoverCartesianFoldStepProof (onCons)
open NumberedWindowInternalCoverCartesianFoldNumericProof (exact_CartesianFoldValue)

attribute [local irreducible] programGraph

variable {k : Nat} {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem nilRule (D : Program (k+1)) (source image : OTerm α) (params : Fin k → OTerm α) :
    Nonempty (Derivation body Γ (atList D z source image params)) := by
  let H := memberGraph z source
  have h : Derivation body (H :: Γ) H := Derivation.hypothesis List.mem_cons_self
  have nilValue := nilRecover memberBase memberStep (suc z) (![source] : Fin 1 → OTerm α) ⟨h⟩
  obtain ⟨falseEq⟩ := valueUnique memberBase (suc z) z (![source] : Fin 1 → OTerm α) nilValue (zeroConstantValue _)
  exact ⟨Derivation.implicationIntroduction (Derivation.explosion (sucNeZeroApply falseEq))⟩

private theorem consRule (D : Program (k+1)) (raw head tail source deps image : OTerm α)
    (params : Fin k → OTerm α) (cell : Nonempty (Derivation body Γ (consGraph raw head tail)))
    (known : Nonempty (Derivation body Γ (programGraph D deps (Fin.cons source params))))
    (selected : Nonempty (Derivation body Γ (memberGraph deps image)))
    (ih : Nonempty (Derivation body Γ (atList D tail source image params))) :
    Nonempty (Derivation body Γ (atList D raw source image params)) := by
  let H := memberGraph raw source
  let Δ := H :: Γ
  have member : Nonempty (Derivation body Δ H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have imageIn : Nonempty (Derivation body Δ (imageGraph D raw image params)) := by
    apply programCases (flatMap D) (Fin.cons raw params) _
    intro β j Θ out keep run
    rw [imageRename]
    simp only [consTermRename] at run
    have cell' := renameInto (withHyp cell H) j Θ keep
    have known' := renameInto (withHyp known H) j Θ keep
    have selected' := renameInto (withHyp selected H) j Θ keep
    have ih' := renameInto (withHyp ih H) j Θ keep
    have member' := renameInto member j Θ keep
    simp only [consGraphRename] at cell'
    simp only [programRename,consTermRename] at known'
    simp only [graphRename,H] at selected' member'
    simp only [atListRename] at ih'
    let p := fun i => (params i).relabel j
    exact imageOfMember D out (raw.relabel j) (image.relabel j) p run
      (onCons D (raw.relabel j) (head.relabel j) (tail.relabel j) (source.relabel j)
        (deps.relabel j) (image.relabel j) out p cell' member' known' selected' run ih')
  obtain ⟨hit⟩ := imageIn
  exact ⟨Derivation.implicationIntroduction hit⟩

private theorem allCons (D : Program (k+1)) (source deps image : OTerm α) (params : Fin k → OTerm α)
    (known : Nonempty (Derivation body Γ (programGraph D deps (Fin.cons source params))))
    (selected : Nonempty (Derivation body Γ (memberGraph deps image))) :
    Nonempty (Derivation body Γ (constructors (motive D source image params))) := by
  apply actualFiniteUniversalIntroduction body α 3 Γ (constructorBody (motive D source image params))
  let j : α → α ⊕ Fin 3 := Sum.inl
  let raw : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let head : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let tail : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let p := fun i => (params i).relabel j
  let H := consGraph raw head tail
  let Old := atList D tail (source.relabel j) (image.relabel j) p
  let Δ := Old :: H :: Γ.map (fun h => h.relabel j)
  change Nonempty (Derivation body (Γ.map (fun h => h.relabel j))
    (H.imp ((atIndex (motive D source image params) 2).imp (atIndex (motive D source image params) 0))))
  simp only [atIndexEq]
  have keep : ∀ q ∈ Γ, q.relabel j ∈ Δ := by
    intro q h
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,h,rfl⟩))
  have known' := renameInto known j Δ keep
  have selected' := renameInto selected j Δ keep
  simp only [programRename,consTermRename] at known'
  simp only [graphRename] at selected'
  obtain ⟨d⟩ := consRule D raw head tail (source.relabel j) (deps.relabel j) (image.relabel j) p
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩ known' selected'
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩

theorem exact_OpenCartesianFoldMember : ExactOpenCartesianFoldMember := by
  intro k D body α Γ raw source deps image out params member known selected run
  have nil : Nonempty (Derivation body Γ (atCode (motive D source image params) z)) := by
    rw [atCodeEq]
    exact nilRule D source image params
  obtain ⟨base⟩ := nil
  obtain ⟨step⟩ := allCons D source deps image params known selected
  have all := actualOriginalListInductionAtCode body α Γ (motive D source image params) raw
    ⟨Derivation.conjunctionIntroduction base step⟩
  rw [atCodeEq] at all
  obtain ⟨applyLaw⟩ := all
  obtain ⟨inSource⟩ := member
  exact memberOfImage D out raw image params run ⟨Derivation.implicationElimination applyLaw inSource⟩

#print axioms exact_CartesianFoldValue
#print axioms exact_OpenCartesianFoldMember

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldChecks
