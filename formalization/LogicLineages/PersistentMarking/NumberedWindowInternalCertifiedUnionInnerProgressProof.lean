module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionProgressSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionInnerProgressProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.SourcePresentation ID1Completion.InternalCalculus
open ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.SourceComputabilityCompletion.InverseApplicationSyntaxProof (membershipRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalDirectCoreNumericTargets (CountFit)
open NumberedWindowInternalCertifiedUnionStepProof
open NumberedWindowInternalCertifiedUnionInnerSyntaxProof
open NumberedWindowInternalCertifiedUnionInnerInductionProof (exact_RestoreActualInnerMembership)
open NumberedWindowInternalCertifiedUnionProgressSupportProof

/-- Still unpaid: object-calculus typedness of the actual accepted packed
union, using the two actual component carriers and the same observer. -/
def UnionCarrierSupply (data : Data) (c : Nat) (count : Program 2) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (a b u : OTerm α),
    Pr data c Γ (carrier data true c a) →
    Pr data c Γ (carrier data true c b) →
    Pr data c Γ (unionGraph count a b u) →
    Pr data c Γ (carrier data true c u)

/-- The inner consequence of literal union, under the already-held strict
outer hypothesis and actual lower right states. The certified origin split
and the typed carrier of the recombination stay explicit premises. -/
def ActualCertifiedUnionInnerProgress : Prop :=
  ∀ (data : Data) (c : Nat) (count : Program 2), CountFit count →
    CertifiedOriginSplit data c count → UnionCarrierSupply data c count →
    ∀ (α : Type) (Γ : List (Formula α)) (a b : OTerm α),
      HeldOuter data c count Γ a →
      Pr data c Γ (carrier data true c a) →
      Pr data c Γ (carrier data true c b) →
      Pr data c Γ (innerLower data c count a b) →
      Pr data c Γ (consequence count a b)

theorem exact_ActualCertifiedUnionInnerProgress : ActualCertifiedUnionInnerProgress := by
  intro data c count fit splitter carrierSupply α Γ a b outer ca cb lower
  have hb := exact_RestoreActualInnerMembership data c count Γ a b cb lower
  let a₁ : OTerm (α ⊕ Fin 1) := a.relabel Sum.inl
  let b₁ : OTerm (α ⊕ Fin 1) := b.relabel Sum.inl
  let u : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let P := unionGraph count a₁ b₁ u
  let Γ₁ := P :: Γ.map weaken
  have keeps₁ : Preserves Γ Sum.inl Γ₁ := freshKeeps Γ P
  have outer₁ : HeldOuter data c count Γ₁ a₁ :=
    retainOuter data c count Γ Γ₁ a Sum.inl keeps₁ outer
  have ca₁ := renameInto ca Sum.inl Γ₁ keeps₁
  have cb₁ := renameInto cb Sum.inl Γ₁ keeps₁
  have hb₁ := renameInto hb Sum.inl Γ₁ keeps₁
  have lower₁ := renameInto lower Sum.inl Γ₁ keeps₁
  rw [oddCarrierRename] at ca₁ cb₁
  rw [membershipRename] at hb₁
  rw [innerLowerRename] at lower₁
  have join₁ : Pr data c Γ₁ (unionGraph count a₁ b₁ u) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have cu₁ : Pr data c Γ₁ (carrier data true c u) :=
    carrierSupply (α ⊕ Fin 1) Γ₁ a₁ b₁ u ca₁ cb₁ join₁
  have answer : Pr data c Γ₁ (membership true u) := by
    apply oddIntroduction data c Γ₁ u cu₁
    intro β j Δ v keep edge
    have keptOuter := retainOuter data c count Γ₁ Δ a₁ j keep outer₁
    have keptRight := renameInto hb₁ j Δ keep
    have keptLower := renameInto lower₁ j Δ keep
    have keptCarrier := renameInto cu₁ j Δ keep
    have keptJoin := renameInto join₁ j Δ keep
    rw [membershipRename] at keptRight
    rw [innerLowerRename] at keptLower
    rw [oddCarrierRename] at keptCarrier
    rw [unionGraphRename] at keptJoin
    apply oddCertificateCases data c Δ (u.relabel j) v (membership true v) edge
    intro γ k Ξ w nextKeeps cert
    have out := retainOuter data c count Δ Ξ (a₁.relabel j) k nextKeeps keptOuter
    have right := renameInto keptRight k Ξ nextKeeps
    have early := renameInto keptLower k Ξ nextKeeps
    have carrierU := renameInto keptCarrier k Ξ nextKeeps
    have sameJoin := renameInto keptJoin k Ξ nextKeeps
    rw [membershipRename] at right ⊢
    rw [innerLowerRename] at early
    rw [oddCarrierRename] at carrierU
    rw [unionGraphRename] at sameJoin
    exact exact_OriginalCertifiedUnionStep data c count fit splitter γ Ξ
      ((a₁.relabel j).relabel k) ((b₁.relabel j).relabel k) ((u.relabel j).relabel k)
      (v.relabel k) w out
      (heldInnerOfActualLower data c count Ξ _ _ early) right carrierU sameJoin cert
  obtain ⟨proof⟩ := answer
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction proof)⟩

#print axioms exact_ActualCertifiedUnionInnerProgress

end LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionInnerProgressProof
