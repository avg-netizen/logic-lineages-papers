module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRelationalCRTSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRelationalCRTSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalCoprimeMultiple InternalCoprimeMultipleSyntaxProof InternalCoprimeMultipleBoundedProof
open InternalRelationalCRT InternalRelationalCRTSyntaxProof InternalRelationalCRTChoiceProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalTermSubstitutionSyntaxProof
open InternalPositiveUnfoldingSupportProof InternalLeastNumberSyntaxProof InternalBinaryCRTSyntaxProof
open InternalBezoutExistenceTargets InternalDivisibilityProof InternalOriginalOrderSyntaxProof
open InternalOriginalOrderProof InternalModularArithmeticProof InternalSourceIntroductionSyntaxProof
open InternalGraphCompositionSyntaxProof InternalFiniteBlocksSubstitutionProof

/-- Substitute only the index, leaving the original residue variable free. -/
def atIndex {α : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (n : OTerm α) : Formula (α ⊕ Fin 1) :=
  R.subst (fun x => emb (liftTerms (bindTerm n) x))

theorem atIndexRename {α β : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (n : OTerm α) (j : α → β) :
    (atIndex R n).relabel (Sum.map j id) =
      atIndex (R.relabel (Sum.map (Sum.map j id) id)) (n.relabel j) := by
  unfold atIndex
  rw [formulaSubstRelabel,actualRelabelSubstitution]
  congr 1
  funext x
  rcases x with (a | i) | k
  · rfl
  · simp only [Function.comp_apply,liftTerms,bindTerm,Sum.elim_inl,Sum.elim_inr,Sum.map_inl,Sum.map_inr]
    rw [← onTermRelabel]
    congr 1
    rw [Term.relabel_relabel,Term.relabel_relabel]
    rfl
  · rfl

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
theorem availableLast (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (n : OTerm α)
    (h : Nonempty (Derivation body Gamma (availableBelow R (suc n)))) :
    Nonempty (Derivation body Gamma (existsOne (atIndex R n))) := by
  obtain ⟨h⟩ := h
  obtain ⟨hn⟩ := selfLtSucc (body := body) (Gamma := Gamma) n
  have h := boundedElim _ n (suc n) h hn
  rw [instantiate,bindEmbedding,existsSubst,liftEmbedding] at h
  exact ⟨h⟩

theorem solutionZero (t : OTerm (α ⊕ Fin 1)) (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) :
    Nonempty (Derivation body Gamma (solution t R z)) := by
  exact solutionIntroduction t R z z (boundedZero _)

/-- Preserve every original relation witness while transporting the shared code. -/
theorem preserveResidues (t : OTerm (α ⊕ Fin 1)) (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (n P c d : OTerm α)
    (hd : Nonempty (Derivation body Gamma (dividesBelow t P n)))
    (hc : Nonempty (Derivation body Gamma (cf d c P)))
    (hr : Nonempty (Derivation body Gamma (residuesBelow t R c n))) :
    Nonempty (Derivation body Gamma (residuesBelow t R d n)) := by
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
  obtain ⟨he⟩ := chosenTransport R (suc t) (c.relabel Sum.inl) (d.relabel Sum.inl) he ⟨hr'⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction he)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRelationalCRTSupportProof
