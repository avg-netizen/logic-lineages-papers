module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionConsumerProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalSourceInversionSupportProof InternalPositiveUnfoldingSupportProof InternalAdditionLawsProof
open InternalCoprimeMultiple InternalCoprimeMultipleSyntaxProof InternalCoprimeMultipleBoundedProof
open InternalBinderTransportSyntaxProof InternalTermSubstitutionSyntaxProof
open InternalFiniteBlocksSubstitutionProof InternalBetaTotalitySyntaxProof
open InternalBetaExtension InternalBetaExtensionSyntaxProof InternalBetaExtensionProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Both implications at arbitrary object terms, obtained from the literal prefix universal. -/
def sameBelowElim (a b c d n i r : OTerm α)
    (h : Derivation body Gamma (sameBelow a b c d n))
    (hi : Derivation body Gamma (InternalOriginalOrderSyntaxProof.ltF i n)) :
    Derivation body Gamma ((beta a b i r).imp (beta c d i r) ⊓
      (beta c d i r).imp (beta a b i r)) := by
  have h := boundedElim _ i n h hi
  rw [instantiate,bindEmbedding,sameAtSubst] at h
  simp only [liftBind,varBind] at h
  have h := Derivation.universalElimination (emb r) h
  simp only [sameAt,infInstantiate,impInstantiate,beta,betaInstantiate,liftBind,varBind] at h
  exact h

theorem extensionWithCases (Gamma : List (Formula α)) (a b n z c : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (extensionWith a b n z c)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (d : OTerm β),
      (∀ f ∈ Gamma, f.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (extensionMatrix (a.relabel j) (b.relabel j)
        (n.relabel j) (z.relabel j) (c.relabel j) d)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  obtain ⟨hk⟩ := k (α ⊕ Fin 1) Sum.inl _ (.var (.inr 0))
    (by intro f hf; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.existentialElimination h hk⟩

/-- Eliminate the shared pair while preserving every caller parameter and hypothesis. -/
theorem extensionCases (Gamma : List (Formula α)) (a b n z : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (extension a b n z)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (c d : OTerm β),
      (∀ f ∈ Gamma, f.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (extensionMatrix (a.relabel j) (b.relabel j)
        (n.relabel j) (z.relabel j) c d)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  let c : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let mat := extensionWith (a.relabel Sum.inl) (b.relabel Sum.inl) (n.relabel Sum.inl)
    (z.relabel Sum.inl) c
  let Delta := mat :: Gamma.map weaken
  have hm : Nonempty (Derivation body Delta mat) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have he : Nonempty (Derivation body Delta (psi.relabel Sum.inl)) := by
    apply extensionWithCases Delta _ _ _ _ c (psi.relabel Sum.inl) hm
    intro β j Theta d hj hd
    simp only [Term.relabel_relabel] at hd
    rw [formulaRelabelComposition]
    apply k β (j ∘ Sum.inl) Theta (c.relabel j) d _ hd
    intro f hf
    have hmem : f.relabel Sum.inl ∈ Delta :=
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
    have hmem := hj (f.relabel Sum.inl) hmem
    simpa only [formulaRelabelComposition] using hmem
  obtain ⟨he⟩ := he
  exact ⟨Derivation.existentialElimination h he⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionConsumerProof
