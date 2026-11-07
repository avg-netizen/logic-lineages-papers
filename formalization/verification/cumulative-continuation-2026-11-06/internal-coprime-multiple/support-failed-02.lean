module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBoundedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalProductCoprimalityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalAdditionLawsProof InternalMultiplicationLawsProof InternalLinearCombinationSyntaxProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalLeastNumberSyntaxProof
open InternalCoprimeMultiple InternalCoprimeMultipleSyntaxProof InternalCoprimeMultipleBoundedProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalPositiveUnfoldingSupportProof
open InternalBezoutExistenceTargets InternalDivisibilityProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

def coprimeCongruence (a b c : OTerm α) (he : Derivation body Gamma (eqn b c))
    (h : Derivation body Gamma (coprime a b)) : Derivation body Gamma (coprime a c) := by
  let p : Formula (α ⊕ Fin 1) := coprime (a.relabel (Sum.inl : α → α ⊕ Fin 1)) (.var (.inr 0))
  have hb : Derivation body Gamma (instantiate p (emb b)) := by
    simp only [p,coprimeInstantiate,liftBind,varBind]; exact h
  have hc := Derivation.equalityElimination p (emb b) (emb c) he hb
  simpa only [p,coprimeInstantiate,liftBind,varBind] using hc

def dividesBelowCongruence (t : OTerm (α ⊕ Fin 1)) (P Q n : OTerm α)
    (he : Derivation body Gamma (eqn P Q)) (h : Derivation body Gamma (dividesBelow t P n)) :
    Derivation body Gamma (dividesBelow t Q n) := by
  let p : Formula (α ⊕ Fin 1) := dividesBelow (t.relabel (Sum.map Sum.inl id)) (.var (.inr 0)) (n.relabel Sum.inl)
  have hb : Derivation body Gamma (instantiate p (emb P)) := by
    simp only [p,instantiate,bindEmbedding,dividesBelowSubst,termLiftBind,varBind,liftBind]; exact h
  have hc := Derivation.equalityElimination p (emb P) (emb Q) he hb
  simpa only [p,instantiate,bindEmbedding,dividesBelowSubst,termLiftBind,varBind,liftBind] using hc

theorem commonIntroduction (a : OTerm α) (t : OTerm (α ⊕ Fin 1)) (n p : OTerm α)
    (hc : Nonempty (Derivation body Gamma (coprime a (suc p))))
    (hd : Nonempty (Derivation body Gamma (dividesBelow t (suc p) n))) :
    Nonempty (Derivation body Gamma (commonMultiple a t n)) := by
  obtain ⟨hc⟩ := hc
  obtain ⟨hd⟩ := hd
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb p)
  rw [commonMatrixInstantiate]
  exact Derivation.conjunctionIntroduction hc hd

theorem commonCases (Gamma : List (Formula α)) (a : OTerm α) (t : OTerm (α ⊕ Fin 1))
    (n : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (commonMultiple a t n)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (p : OTerm β),
      (∀ f ∈ Gamma, f.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (coprime (a.relabel j) (suc p))) →
      Nonempty (Derivation body Delta (dividesBelow (t.relabel (Sum.map j id)) (suc p) (n.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  apply Derivation.existentialElimination h
  let mat : Formula (α ⊕ Fin 1) := coprime (a.relabel Sum.inl) (suc (.var (.inr 0))) ⊓
    dividesBelow (t.relabel (Sum.map Sum.inl id)) (suc (.var (.inr 0))) (n.relabel Sum.inl)
  have hm : Derivation body (mat :: Gamma.map weaken) mat := Derivation.hypothesis List.mem_cons_self
  obtain ⟨hk⟩ := k (α ⊕ Fin 1) Sum.inl _ (.var (.inr 0))
    (by intro f hf; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
    ⟨Derivation.conjunctionLeft hm⟩ ⟨Derivation.conjunctionRight hm⟩
  exact hk
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleSupportProof
