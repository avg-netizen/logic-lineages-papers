module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionOuterAccessProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionOuterInductionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.SourcePresentation ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm emb)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalDirectCoreNumericTargets (CountFit)
open NumberedWindowInternalCertifiedUnionStepProof
open NumberedWindowInternalCertifiedUnionInnerSyntaxProof
open NumberedWindowInternalCertifiedUnionInnerProgressProof
open NumberedWindowInternalCertifiedUnionProgressSupportProof
open NumberedWindowInternalCertifiedUnionOuterSyntaxProof
open NumberedWindowInternalCertifiedUnionOuterAccessProof
open NumberedWindowInternalOddProgressiveInductionProof

theorem actualOuterProgress {α : Type} (data : Data) (c : Nat) (count : Program 2)
    (fit : CountFit count) (splitter : CertifiedOriginSplit data c count)
    (supply : UnionCarrierSupply data c count) (Γ : List (Formula α)) (a : OTerm α)
    (typed : Pr data c Γ (carrier data true c a))
    (lower : Pr data c Γ (outerLower data c count a)) :
    Pr data c Γ (outerState count a) := by
  obtain ⟨leftJ⟩ := restoreOuterMembership data c count Γ a typed lower
  let b : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let a₁ : OTerm (α ⊕ Fin 1) := a.relabel Sum.inl
  let Δ := Γ.map weaken
  have keeps : Preserves Γ Sum.inl Δ := by
    intro p hp
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have newTyped := renameInto typed Sum.inl Δ keeps
  rw [oddCarrierRename] at newTyped
  obtain ⟨finish⟩ := actualRightInduction data c count fit splitter supply Δ a₁ b
    newTyped (retainOuter data c count Γ Δ a Sum.inl keeps
      (heldOuterOfActualLower data c count Γ a lower))
  let P := membership true b
  have h : Derivation (sourceBody data c) (P :: Δ) (P.imp (innerState count a₁ b)) :=
    Derivation.weakening (fun _ h => List.mem_cons_of_mem _ h) finish
  have result : Derivation (sourceBody data c) (P :: Δ) (consequence count a₁ b) :=
    Derivation.conjunctionRight (Derivation.implicationElimination h
      (Derivation.hypothesis List.mem_cons_self))
  exact ⟨Derivation.conjunctionIntroduction leftJ
    (Derivation.universalIntroduction (Derivation.implicationIntroduction result))⟩

theorem exact_ActualCertifiedUnionOuterInduction {α : Type} (data : Data) (c : Nat)
    (count : Program 2) (fit : CountFit count) (splitter : CertifiedOriginSplit data c count)
    (supply : UnionCarrierSupply data c count) (Γ : List (Formula α)) (a : OTerm α) :
    Pr data c Γ ((membership true a).imp (outerState count a)) := by
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let T := carrier data true c x
  let L := outerLower data c count x
  let Δ := T :: L :: Γ.map weaken
  have progress : Pr data c
      (T :: oddLower data c x (outerMotive (α := α) count) :: Γ.map weaken)
      (outerMotive (α := α) count) := by
    rw [literalOuterOddLower]
    exact actualOuterProgress data c count fit splitter supply Δ x
      ⟨Derivation.hypothesis List.mem_cons_self⟩
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have result := exact_ActualOriginalOddProgressiveInduction data c α Γ (outerMotive count) a progress
  rw [outerMotiveAt] at result
  exact result

/-- Conditional union in the original source calculus, under actual
original memberships and actual occurrence-checked packed union. -/
def ActualOriginalConditionalJUnion : Prop :=
  ∀ (data : Data) (c : Nat) (count : Program 2),
    CountFit count → CertifiedOriginSplit data c count → UnionCarrierSupply data c count →
    ∀ (α : Type) (Γ : List (Formula α)) (a b u : OTerm α),
      Pr data c Γ (membership true a) →
      Pr data c Γ (membership true b) →
      Pr data c Γ (unionGraph count a b u) →
      Pr data c Γ (membership true u)

theorem exact_ActualOriginalConditionalJUnion : ActualOriginalConditionalJUnion := by
  intro data c count fit splitter supply α Γ a b u left right joined
  obtain ⟨ind⟩ := exact_ActualCertifiedUnionOuterInduction data c count fit splitter supply Γ a
  obtain ⟨ha⟩ := left
  have claim : Pr data c Γ (outerClaim count a) :=
    ⟨Derivation.conjunctionRight (Derivation.implicationElimination ind ha)⟩
  exact consequenceApply data c count Γ a b u
    (actualOuterClaimApply data c count Γ a b claim right) joined

#print axioms exact_ActualCertifiedUnionOuterInduction
#print axioms exact_ActualOriginalConditionalJUnion

end LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionOuterInductionProof
