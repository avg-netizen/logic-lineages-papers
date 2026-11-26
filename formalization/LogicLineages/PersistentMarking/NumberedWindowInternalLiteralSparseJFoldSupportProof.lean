module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSparseJFoldSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSparseJFoldSupportProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn bindEmbedding varBind)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (membershipSubst)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (tailMember)
open NumberedWindowInternalLiteralSparseJFoldSyntaxProof
open NumberedWindowInternalCertifiedUnionProgressSupportProof (freshKeeps)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem applyScalarMembers (s q : OTerm α)
    (all : Nonempty (Derivation B Γ (scalarMembers s)))
    (occurs : Nonempty (Derivation B Γ (memberGraph s q))) :
    Nonempty (Derivation B Γ (membership false q)) := by
  obtain ⟨all⟩ := all
  obtain ⟨occurs⟩ := occurs
  have member := Derivation.universalElimination (emb q) all
  rw [scalarMembersAt] at member
  exact ⟨Derivation.implicationElimination member occurs⟩

/-- Retain the same original cons, with each actual tail occurrence
transported into the actual parent scratch before the scalar premise. -/
theorem scalarMembersOfTail (s h st : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph s h st)))
    (all : Nonempty (Derivation B Γ (scalarMembers s))) :
    Nonempty (Derivation B Γ (scalarMembers st)) := by
  let q : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let P := memberGraph (st.relabel Sum.inl) q
  let Δ := P :: Γ.map weaken
  have mapped := renameInto cell Sum.inl Δ (freshKeeps Γ P)
  rw [consGraphRename] at mapped
  have kept := renameInto all Sum.inl Δ (freshKeeps Γ P)
  rw [scalarMembersRename] at kept
  have mem : Nonempty (Derivation B Δ P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have orig := tailMember (s.relabel Sum.inl) (h.relabel Sum.inl) (st.relabel Sum.inl) q mapped mem
  obtain ⟨done⟩ := applyScalarMembers (s.relabel Sum.inl) q kept orig
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction done)⟩

theorem moveJ (n m : OTerm α)
    (same : Nonempty (Derivation B Γ (eqn n m)))
    (h : Nonempty (Derivation B Γ (membership true n))) :
    Nonempty (Derivation B Γ (membership true m)) := by
  obtain ⟨same⟩ := same
  obtain ⟨h⟩ := h
  let theta : Formula (α ⊕ Fin 1) := membership true (.var (.inr 0))
  have transport := Derivation.equalityElimination theta (emb n) (emb m) same
  simp only [theta,instantiate,bindEmbedding,membershipSubst,varBind] at transport
  exact ⟨transport h⟩

theorem addTwoHypotheses {f : Formula α} (p q : Formula α)
    (h : Nonempty (Derivation B Γ f)) : Nonempty (Derivation B (q :: p :: Γ) f) := by
  obtain ⟨h⟩ := h
  exact ⟨addHyp (addHyp h p) q⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSparseJFoldSupportProof
