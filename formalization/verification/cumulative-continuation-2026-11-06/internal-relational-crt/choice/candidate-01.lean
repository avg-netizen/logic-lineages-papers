module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRelationalCRTTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCRTProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRelationalCRTChoiceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalCoprimeMultipleSyntaxProof InternalBinderTransportSyntaxProof InternalBinderTransportProof
open InternalTermSubstitutionSyntaxProof InternalTermSubstitutionProof InternalPositiveUnfoldingSupportProof
open InternalDerivationRenamingSyntaxProof InternalLeastNumberSyntaxProof InternalModularArithmeticProof
open InternalBinaryCRTSyntaxProof InternalFiniteBlocksSubstitutionProof InternalOriginalOrderProof
open InternalRelationalCRT

theorem chosenRename {α β : Type} (R : Formula (α ⊕ Fin 1)) (m c : OTerm α) (j : α → β) :
    (chosen R m c).relabel j = chosen (R.relabel (Sum.map j id)) (m.relabel j) (c.relabel j) := by
  unfold chosen
  rw [existsRename]
  change existsOne (R.relabel (Sum.map j id) ⊓ (cf (c.relabel Sum.inl) (.var (.inr 0))
    (m.relabel Sum.inl)).relabel (Sum.map j id)) = _
  simp only [congruentRename,Term.relabel_relabel,mapInl,varMap]

theorem chosenSubst {α β : Type} (R : Formula (α ⊕ Fin 1)) (m c : OTerm α)
    (ts : α → OTerm β) :
    (chosen R m c).subst (fun x => emb (ts x)) =
      chosen (R.subst (fun x => emb (liftTerms ts x))) (m.subst ts) (c.subst ts) := by
  unfold chosen
  rw [existsSubst,liftEmbedding,infSubst]
  change existsOne (R.subst (fun x => emb (liftTerms ts x)) ⊓
    (cf (c.relabel Sum.inl) (.var (.inr 0)) (m.relabel Sum.inl)).subst
      (fun x => emb (liftTerms ts x))) = _
  simp only [congruentSubst,liftSubst]
  rfl

theorem chosenInstantiate {α : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (m c : OTerm (α ⊕ Fin 1)) (s : OTerm α) :
    instantiate (chosen R m c) (emb s) =
      chosen (R.subst (fun x => emb (liftTerms (bindTerm s) x)))
        (m.subst (bindTerm s)) (c.subst (bindTerm s)) := by
  rw [instantiate,bindEmbedding,chosenSubst]

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
theorem chosenIntroduction (R : Formula (α ⊕ Fin 1)) (m c s : OTerm α)
    (hR : Nonempty (Derivation body Gamma (instantiate R (emb s))))
    (hc : Nonempty (Derivation body Gamma (cf c s m))) :
    Nonempty (Derivation body Gamma (chosen R m c)) := by
  obtain ⟨hR⟩ := hR
  obtain ⟨hc⟩ := hc
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb s)
  change Derivation body Gamma (instantiate R (emb s) ⊓
    instantiate (cf (c.relabel Sum.inl) (.var (.inr 0)) (m.relabel Sum.inl)) (emb s))
  rw [congruentInstantiate,liftBind,varBind,liftBind]
  exact Derivation.conjunctionIntroduction hR hc

theorem existsCases (Gamma : List (Formula α)) (R : Formula (α ⊕ Fin 1)) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (existsOne R)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (s : OTerm β),
      (∀ f ∈ Gamma, f.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (instantiate (R.relabel (Sum.map j id)) (emb s))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  have hR : Nonempty (Derivation body (R :: Gamma.map weaken)
      (instantiate (R.relabel (Sum.map Sum.inl id)) (emb (.var (.inr 0))))) := by
    rw [actualFreshInstantiation]
    exact ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hk⟩ := k (α ⊕ Fin 1) Sum.inl _ (.var (.inr 0))
    (by intro f hf; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)) hR
  exact ⟨Derivation.existentialElimination h hk⟩

theorem chosenCases (Gamma : List (Formula α)) (R : Formula (α ⊕ Fin 1))
    (m c : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (chosen R m c)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (s : OTerm β),
      (∀ f ∈ Gamma, f.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (instantiate (R.relabel (Sum.map j id)) (emb s))) →
      Nonempty (Derivation body Delta (cf (c.relabel j) s (m.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  let mat := R ⊓ cf (c.relabel Sum.inl) (.var (.inr 0)) (m.relabel Sum.inl)
  have hm : Derivation body (mat :: Gamma.map weaken) mat := Derivation.hypothesis List.mem_cons_self
  have hR : Nonempty (Derivation body (mat :: Gamma.map weaken)
      (instantiate (R.relabel (Sum.map Sum.inl id)) (emb (.var (.inr 0))))) := by
    rw [actualFreshInstantiation]
    exact ⟨Derivation.conjunctionLeft hm⟩
  obtain ⟨hk⟩ := k (α ⊕ Fin 1) Sum.inl _ (.var (.inr 0))
    (by intro f hf; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
    hR ⟨Derivation.conjunctionRight hm⟩
  exact ⟨Derivation.existentialElimination h hk⟩

theorem chosenTransport (R : Formula (α ⊕ Fin 1)) (m c d : OTerm α)
    (he : Nonempty (Derivation body Gamma (cf d c m)))
    (hchosen : Nonempty (Derivation body Gamma (chosen R m c))) :
    Nonempty (Derivation body Gamma (chosen R m d)) := by
  apply chosenCases Gamma R m c (chosen R m d) hchosen
  intro β j Delta s hj hR hc
  have he' := renameInto he j Delta hj
  rw [congruentRename] at he'
  have hd := actualTransitivity body β Delta (d.relabel j) (c.relabel j) s (m.relabel j) he' hc
  rw [chosenRename]
  exact chosenIntroduction _ _ _ s hR hd
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRelationalCRTChoiceProof
