module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBoundedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalAdditionLawsProof InternalOriginalOrderSyntaxProof InternalOriginalOrderProof
open InternalLeastNumberSyntaxProof InternalLeastNumberProof InternalCoprimeMultiple InternalCoprimeMultipleSyntaxProof
open InternalPositiveUnfoldingSupportProof InternalBetaTotalityProof InternalBinderTransportProof
open InternalBinderTransportSyntaxProof InternalBetaBoundaryProof InternalQuotientComparisonProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem boundedZero (p : Formula (α ⊕ Fin 1)) :
    Nonempty (Derivation body Gamma (bounded p z)) := by
  obtain ⟨hz⟩ := actualNothingBelowZero body (α ⊕ Fin 1) (.var (.inr 0))
  apply Nonempty.intro
  apply Derivation.universalIntroduction
  simp only [zRelabel]
  apply Derivation.implicationIntroduction
  exact Derivation.explosion (Derivation.implicationElimination
    (weakenClosed hz _) (Derivation.hypothesis List.mem_cons_self))

def boundedElim (p : Formula (α ⊕ Fin 1)) (s n : OTerm α)
    (h : Derivation body Gamma (bounded p n)) (hs : Derivation body Gamma (ltF s n)) :
    Derivation body Gamma (instantiate p (emb s)) := by
  have h := Derivation.universalElimination (emb s) h
  rw [boundedElimSyntax] at h
  exact Derivation.implicationElimination h hs

theorem selfLtSucc (n : OTerm α) : Nonempty (Derivation body Gamma (ltF n (suc n))) := by
  apply actualOriginalOrderIntroduction body α Gamma n (suc n) z
  rw [onEquality]
  exact ⟨trans (addSucc n z) (congSuc (addZero n))⟩

theorem boundedRestrict (p : Formula (α ⊕ Fin 1)) (n : OTerm α)
    (h : Nonempty (Derivation body Gamma (bounded p (suc n)))) :
    Nonempty (Derivation body Gamma (bounded p n)) := by
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let N := n.relabel (Sum.inl : α → α ⊕ Fin 1)
  let Delta := ltF x N :: Gamma.map weaken
  have hi : ∀ q ∈ Gamma, q.relabel Sum.inl ∈ Delta := by
    intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have h' := renameInto h Sum.inl Delta hi
  rw [boundedRename,sucRelabel] at h'
  obtain ⟨h'⟩ := h'
  obtain ⟨hn⟩ := selfLtSucc (body := body) (Gamma := Delta) N
  obtain ⟨ht⟩ := actualOriginalOrderTransitivity body (α ⊕ Fin 1) x N (suc N)
  have hx : Derivation body Delta (ltF x (suc N)) :=
    Derivation.implicationElimination (weakenClosed ht Delta)
      (Derivation.conjunctionIntroduction (Derivation.hypothesis List.mem_cons_self) hn)
  have hp := boundedElim (liftP p) x (suc N) h' hx
  rw [show x = .var (.inr 0) from rfl,freshP] at hp
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction hp)⟩

theorem boundedStep (p : Formula (α ⊕ Fin 1)) (n : OTerm α)
    (hb : Nonempty (Derivation body Gamma (bounded p n)))
    (hn : Nonempty (Derivation body Gamma (instantiate p (emb n)))) :
    Nonempty (Derivation body Gamma (bounded p (suc n))) := by
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let N := n.relabel (Sum.inl : α → α ⊕ Fin 1)
  let Delta := ltF x (suc N) :: Gamma.map weaken
  have hi : ∀ q ∈ Gamma, q.relabel Sum.inl ∈ Delta := by
    intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have hb' := renameInto hb Sum.inl Delta hi
  rw [boundedRename] at hb'
  obtain ⟨hb'⟩ := hb'
  have hn' := renameInto hn Sum.inl Delta hi
  rw [instantiateRename, ← InternalBinderTransportSyntaxProof.onTermRelabel] at hn'
  obtain ⟨hn'⟩ := hn'
  obtain ⟨split⟩ := actualRightSuccessorSplit body (α ⊕ Fin 1) x N
  change Derivation body [] ((ltF x (suc N)).imp (ltF x N ⊔ arithmeticEmbedding.onFormula (x.equal N))) at split
  rw [onEquality] at split
  have hd := Derivation.implicationElimination (weakenClosed split Delta) (Derivation.hypothesis List.mem_cons_self)
  have hl : Derivation body Delta ((ltF x N).imp p) := by
    apply Derivation.implicationIntroduction
    have hh := boundedElim (liftP p) x N (addHyp hb' _) (Derivation.hypothesis List.mem_cons_self)
    simpa only [x,freshP] using hh
  have hr : Derivation body Delta ((eqn x N).imp p) := by
    apply Derivation.implicationIntroduction
    have he : Derivation body (eqn x N :: Delta) (eqn x N) := Derivation.hypothesis List.mem_cons_self
    have hh := Derivation.equalityElimination (liftP p) (emb N) (emb x) (symm he) (addHyp hn' _)
    simpa only [x,freshP] using hh
  have hp := disjunctionElimination hd hl hr
  apply Nonempty.intro
  apply Derivation.universalIntroduction
  simp only [sucRelabel]
  exact Derivation.implicationIntroduction hp
theorem boundedMap (p q : Formula (α ⊕ Fin 1)) (n : OTerm α)
    (h : Nonempty (Derivation body Gamma (bounded p n)))
    (hk : Nonempty (Derivation body Gamma (allOne (p.imp q)))) :
    Nonempty (Derivation body Gamma (bounded q n)) := by
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let N := n.relabel (Sum.inl : α → α ⊕ Fin 1)
  let Delta := ltF x N :: Gamma.map weaken
  have hi : ∀ r ∈ Gamma, r.relabel Sum.inl ∈ Delta := by
    intro r hr; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r,hr,rfl⟩)
  have h' := renameInto h Sum.inl Delta hi
  rw [boundedRename] at h'
  obtain ⟨h'⟩ := h'
  obtain ⟨hk'⟩ := renameInto hk Sum.inl Delta hi
  have hk' := InternalBezoutExistenceConsumerProof.freshUniversal hk'
  have hp := boundedElim (liftP p) x N h' (Derivation.hypothesis List.mem_cons_self)
  rw [show x = .var (.inr 0) from rfl,freshP] at hp
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction
    (Derivation.implicationElimination hk' hp))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBoundedProof
