module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionOuterSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionOuterAccessProof
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
open NumberedWindowInternalCertifiedUnionInnerInductionProof
open NumberedWindowInternalCertifiedUnionInnerProgressProof
open NumberedWindowInternalCertifiedUnionProgressSupportProof
open NumberedWindowInternalCertifiedUnionOuterSyntaxProof

theorem actualOuterStateAt {α : Type} (data : Data) (c : Nat) (count : Program 2)
    (Γ : List (Formula α)) (a y : OTerm α) :
    Pr data c Γ (outerLower data c count a) →
    Pr data c Γ (edge data true c a y) →
    Pr data c Γ (outerState count y) := by
  rintro ⟨lower⟩ ⟨step⟩
  have h := Derivation.universalElimination (emb y) lower
  rw [outerLowerAt] at h
  exact ⟨Derivation.implicationElimination h step⟩

theorem actualOuterClaimApply {α : Type} (data : Data) (c : Nat) (count : Program 2)
    (Γ : List (Formula α)) (a b : OTerm α) :
    Pr data c Γ (outerClaim count a) →
    Pr data c Γ (membership true b) →
    Pr data c Γ (consequence count a b) := by
  rintro ⟨claim⟩ ⟨right⟩
  have h := Derivation.universalElimination (emb b) claim
  rw [outerClaimAt] at h
  exact ⟨Derivation.implicationElimination h right⟩

theorem heldOuterOfActualLower {α : Type} (data : Data) (c : Nat) (count : Program 2)
    (Γ : List (Formula α)) (a : OTerm α)
    (lower : Pr data c Γ (outerLower data c count a)) :
    HeldOuter data c count Γ a := by
  intro β j Δ a' b' u' keep strict right joined
  have moved := renameInto lower j Δ keep
  rw [outerLowerRename] at moved
  obtain ⟨h⟩ := actualOuterStateAt data c count Δ (a.relabel j) a' moved strict
  exact consequenceApply data c count Δ a' b' u'
    (actualOuterClaimApply data c count Δ a' b' ⟨Derivation.conjunctionRight h⟩ right) joined

/-- Current left J is paid from the typed carrier and all strict lower
outer states, not a premise of the original odd progress step. -/
theorem restoreOuterMembership {α : Type} (data : Data) (c : Nat) (count : Program 2)
    (Γ : List (Formula α)) (a : OTerm α)
    (typed : Pr data c Γ (carrier data true c a))
    (lower : Pr data c Γ (outerLower data c count a)) : Pr data c Γ (membership true a) := by
  apply oddIntroduction data c Γ a typed
  intro β j Δ y keep strict
  have moved := renameInto lower j Δ keep
  rw [outerLowerRename] at moved
  obtain ⟨h⟩ := actualOuterStateAt data c count Δ (a.relabel j) y moved strict
  exact ⟨Derivation.conjunctionLeft h⟩

/-- Apply the checked inner odd induction to an arbitrary literal right
term, with the outer progress hypotheses kept under its fresh binder. -/
theorem actualRightInduction {α : Type} (data : Data) (c : Nat) (count : Program 2)
    (fit : CountFit count) (splitter : CertifiedOriginSplit data c count)
    (supply : UnionCarrierSupply data c count)
    (Γ : List (Formula α)) (a b : OTerm α)
    (typed : Pr data c Γ (carrier data true c a))
    (outer : HeldOuter data c count Γ a) :
    Pr data c Γ ((membership true b).imp (innerState count a b)) := by
  apply exact_ActualCertifiedUnionInnerInduction data c count α Γ a b
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let a₁ : OTerm (α ⊕ Fin 1) := a.relabel Sum.inl
  let Jx := membership true x
  let Tx := carrier data true c x
  let Lx := innerLower data c count a₁ x
  let Δ := Jx :: Tx :: Lx :: Γ.map weaken
  have keeps : Preserves Γ Sum.inl Δ := by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)))
  have newTyped := renameInto typed Sum.inl Δ keeps
  rw [oddCarrierRename] at newTyped
  have currentTyped : Pr data c Δ Tx :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have currentLower : Pr data c Δ Lx :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
  exact exact_ActualCertifiedUnionInnerProgress data c count fit splitter supply
    (α ⊕ Fin 1) Δ a₁ x (retainOuter data c count Γ Δ a Sum.inl keeps outer)
    newTyped currentTyped currentLower

#print axioms actualRightInduction

end LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionOuterAccessProof
