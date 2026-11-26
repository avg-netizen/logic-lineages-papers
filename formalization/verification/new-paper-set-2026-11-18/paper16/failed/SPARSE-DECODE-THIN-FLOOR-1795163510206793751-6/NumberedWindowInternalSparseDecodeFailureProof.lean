module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodePreimageProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSuccessProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeFailureProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open NumberedWindowInternalSparseDecode NumberedWindowInternalSparseDecodeTargets
open NumberedWindowInternalSparseDecodeSyntaxProof NumberedWindowInternalSparseDecodeGuardProof
open NumberedWindowInternalSparseDecodeSuccessProof NumberedWindowInternalSparseDecodePreimageProof

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem carry {φ : Formula α} (A : Formula (α ⊕ Fin 1))
    (h : Nonempty (Derivation body Γ φ)) :
    Nonempty (Derivation body (A :: Γ.map weaken) (φ.relabel (Sum.inl : α → α ⊕ Fin 1))) :=
  renameInto h Sum.inl _ (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))

private theorem preimageOfGood (n : OTerm α) (hg : Nonempty (Derivation body Γ (unary good (suc z) n))) :
    Nonempty (Derivation body Γ (hasPreimage n)) := by
  apply programCases leftCandidate ![n] (hasPreimage n)
  intro β j Δ x hJ hx
  rw [preimageRename]
  let nn := n.relabel j
  change Nonempty (Derivation body Δ (unary leftCandidate x nn)) at hx
  have good' := renameInto hg j Δ hJ
  rw [unaryRename,sucRelabel,zRelabel] at good'
  apply programCases rightCandidate ![nn] (hasPreimage nn)
  intro γ k Θ y hK hy
  rw [preimageRename]
  let m := nn.relabel k
  let a := x.relabel k
  change Nonempty (Derivation body Θ (unary rightCandidate y m)) at hy
  have left' := renameInto hx k Θ hK
  rw [unaryRename] at left'
  have accepted := renameInto good' k Θ hK
  rw [unaryRename,sucRelabel,zRelabel] at accepted
  obtain ⟨left'⟩ := left'
  obtain ⟨right'⟩ := hy
  obtain ⟨accepted⟩ := accepted
  have cert : Nonempty (Derivation body Θ (certifiedOutputs m a y)) :=
    ⟨Derivation.conjunctionIntroduction accepted (Derivation.conjunctionIntroduction left' right')⟩
  exact preimageIntro m a y (successToPair m a y cert)

private theorem noPreimageOfRejected (n : OTerm α)
    (h : Nonempty (Derivation body Γ (unary good z n))) :
    Nonempty (Derivation body Γ (hasPreimage n).not) := by
  obtain ⟨h⟩ := h
  let E := hasPreimage n
  let Γ₀ := E :: Γ
  let L : α → α ⊕ Fin 1 := Sum.inl
  let M : α ⊕ Fin 1 → (α ⊕ Fin 1) ⊕ Fin 1 := Sum.inl
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let y : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inr 0)
  let A := second (n.relabel L) x
  let Δ := A :: Γ₀.map weaken
  let nn := (n.relabel L).relabel M
  let xx := x.relabel M
  let B := binary sparsePair nn xx y
  let Θ := B :: Δ.map weaken
  have r₁ := carry A (Γ := Γ₀) ⟨addHyp h E⟩
  change Nonempty (Derivation body Δ ((unary good z n).relabel L)) at r₁
  rw [unaryRename,zRelabel] at r₁
  have r₂ := carry B r₁
  change Nonempty (Derivation body Θ ((unary good z (n.relabel L)).relabel M)) at r₂
  rw [unaryRename,zRelabel] at r₂
  obtain ⟨c⟩ := pairToSuccess nn xx y (Γ := Θ) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨impossible⟩ := valueUnique good (suc z) z ![nn] ⟨Derivation.conjunctionLeft c⟩ r₂
  have inner : Derivation body Δ (⊥ : Formula (α ⊕ Fin 1)) :=
    Derivation.existentialElimination
      (show Derivation body Δ A from Derivation.hypothesis List.mem_cons_self) (sucNeZeroApply impossible)
  have outer : Derivation body Γ₀ (⊥ : Formula α) :=
    Derivation.existentialElimination
      (show Derivation body Γ₀ E from Derivation.hypothesis List.mem_cons_self) inner
  exact ⟨Derivation.implicationIntroduction outer⟩

private theorem rejectedOfNoPreimage (n : OTerm α)
    (h : Nonempty (Derivation body Γ (hasPreimage n).not)) :
    Nonempty (Derivation body Γ (unary good z n)) := by
  obtain ⟨h⟩ := h
  obtain ⟨states⟩ := guardBinary (body := body) (Γ := Γ) n
  let accepted := unary good (suc z) n
  obtain ⟨p⟩ := preimageOfGood (body := body) (Γ := accepted :: Γ) n
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have impossible := Derivation.implicationElimination (addHyp h accepted) p
  exact ⟨disjunctionElimination states
    (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self))
    (Derivation.implicationIntroduction (Derivation.explosion impossible))⟩

theorem openFailure : OpenFailure := by
  intro body α n
  let g := unary good z n
  let s := (hasPreimage n).not
  obtain ⟨h₁⟩ := noPreimageOfRejected (body := body) (Γ := [g]) n
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h₂⟩ := rejectedOfNoPreimage (body := body) (Γ := [s]) n
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction h₁)
    (Derivation.implicationIntroduction h₂)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeFailureProof
