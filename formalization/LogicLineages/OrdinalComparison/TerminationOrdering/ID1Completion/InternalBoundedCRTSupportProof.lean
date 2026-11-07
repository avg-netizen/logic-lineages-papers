module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCRTSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCongruenceDivisorProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCRTSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalCoprimeMultiple InternalCoprimeMultipleSyntaxProof InternalCoprimeMultipleBoundedProof
open InternalBoundedCRT InternalBoundedCRTSyntaxProof InternalModularArithmeticProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalTermSubstitutionSyntaxProof
open InternalPositiveUnfoldingSupportProof InternalLeastNumberSyntaxProof InternalBinaryCRTSyntaxProof InternalDerivationRenamingSyntaxProof InternalOriginalOrderProof
open InternalBezoutExistenceTargets InternalDivisibilityProof InternalOriginalOrderSyntaxProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem pairwiseLast (t : OTerm (α ⊕ Fin 1)) (n : OTerm α)
    (h : Nonempty (Derivation body Gamma (pairwiseBelow t (suc n)))) :
    Nonempty (Derivation body Gamma (coprimeBelow (suc (t.subst (bindTerm n))) t n)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hn⟩ := selfLtSucc (body := body) (Gamma := Gamma) n
  have h := boundedElim _ n (suc n) h hn
  rw [instantiate,bindEmbedding,coprimeBelowSubst,termLiftBind,sucSubst,varBind] at h
  exact ⟨h⟩

theorem solutionZero (t r : OTerm (α ⊕ Fin 1)) :
    Nonempty (Derivation body Gamma (InternalBoundedCRT.solution t r z)) := by
  exact InternalBoundedCRTSyntaxProof.solutionIntroduction t r z z (boundedZero _)

/-- Divisibility into a shared modulus transports a new code to all old residues. -/
theorem preserveResidues (t r : OTerm (α ⊕ Fin 1)) (n P c d : OTerm α)
    (hd : Nonempty (Derivation body Gamma (dividesBelow t P n)))
    (hc : Nonempty (Derivation body Gamma (cf d c P)))
    (hr : Nonempty (Derivation body Gamma (residuesBelow t r c n))) :
    Nonempty (Derivation body Gamma (residuesBelow t r d n)) := by
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let N := n.relabel (Sum.inl : α → α ⊕ Fin 1)
  let Delta := ltF x N :: Gamma.map weaken
  have hi : ∀ f ∈ Gamma, f.relabel Sum.inl ∈ Delta := by
    intro f hf; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have hd' := renameInto hd Sum.inl Delta hi
  unfold dividesBelow at hd'
  rw [boundedRename] at hd'
  obtain ⟨hd'⟩ := hd'
  have hd' := boundedElim _ x N hd' (Derivation.hypothesis List.mem_cons_self)
  change Derivation body Delta (instantiate (liftP _) (emb (.var (.inr 0)))) at hd'
  rw [freshP] at hd'
  have hr' := renameInto hr Sum.inl Delta hi
  unfold residuesBelow at hr'
  rw [boundedRename] at hr'
  obtain ⟨hr'⟩ := hr'
  have hr' := boundedElim _ x N hr' (Derivation.hypothesis List.mem_cons_self)
  change Derivation body Delta (instantiate (liftP _) (emb (.var (.inr 0)))) at hr'
  rw [freshP] at hr'
  have hc' := renameInto hc Sum.inl Delta hi
  rw [congruentRename] at hc'
  have he := InternalCongruenceDivisorProof.actualDivisor body (α ⊕ Fin 1) Delta
    (d.relabel Sum.inl) (c.relabel Sum.inl) (suc t) (P.relabel Sum.inl) ⟨hd'⟩ hc'
  obtain ⟨he⟩ := actualTransitivity body (α ⊕ Fin 1) Delta
    (d.relabel Sum.inl) (c.relabel Sum.inl) r (suc t) he ⟨hr'⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction he)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCRTSupportProof
