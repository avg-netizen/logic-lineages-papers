module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationZeroRemainderTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationZeroRemainderProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalQuotientComparisonProof InternalFiniteBlocksSubstitutionProof
open InternalTermSubstitutionSyntaxProof InternalTermSubstitutionProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof
open InternalDerivationRenamingSyntaxProof

def successorExists {α : Type} (r : OTerm α) : Formula α :=
  existsOne (eqn (r.relabel Sum.inl) (suc (.var (.inr (0 : Fin 1)))))

def zeroOrSuccessorFormula {α : Type} (r : OTerm α) : Formula α :=
  eqn r z ⊔ successorExists r

theorem successorExistsSubst {α β : Type} (r : OTerm α) (ts : α → OTerm β) :
    (successorExists r).subst (fun x => emb (ts x)) = successorExists (r.subst ts) := by
  unfold successorExists
  rw [existsSubst]
  let lift : α ⊕ Fin 1 → OTerm (β ⊕ Fin 1) :=
    Sum.elim (fun a => (ts a).relabel Sum.inl) (fun i => .var (.inr i))
  have hf : Sum.elim (fun a => (emb (ts a)).relabel Sum.inl)
      (fun i : Fin 1 => (.var (.inr i) : Term (β ⊕ Fin 1))) = fun a => emb (lift a) := by
    funext a
    cases a with
    | inl a => exact (onTermRelabel arithmeticEmbedding Sum.inl (ts a)).symm
    | inr i => rfl
  have ht : (r.relabel Sum.inl).subst lift = (r.subst ts).relabel Sum.inl := by
    rw [termRelabelSubst,termSubstRelabel]
    rfl
  rw [hf,eqnSubst,sucSubst,ht]
  rfl

theorem successorExistsRename {α β : Type} (r : OTerm α) (j : α → β) :
    (successorExists r).relabel j = successorExists (r.relabel j) := by
  unfold successorExists
  rw [existsRename,eqnRelabel,sucRelabel]
  simp only [Term.relabel_relabel,Term.relabel]
  rfl

theorem zeroOrSuccessorSubst {α β : Type} (r : OTerm α) (ts : α → OTerm β) :
    (zeroOrSuccessorFormula r).subst (fun x => emb (ts x)) =
      zeroOrSuccessorFormula (r.subst ts) := by
  change (eqn r z).subst (fun x => emb (ts x)) ⊔
    (successorExists r).subst (fun x => emb (ts x)) = _
  rw [eqnSubst,zSubst,successorExistsSubst]
  rfl

theorem zeroOrSuccessorInstantiate {α : Type} (r : OTerm (α ⊕ Fin 1)) (u : OTerm α) :
    instantiate (zeroOrSuccessorFormula r) (emb u) =
      zeroOrSuccessorFormula (r.subst (bindTerm u)) := by
  rw [instantiate,bindEmbedding,zeroOrSuccessorSubst]

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

def successorIntroduction (r t : OTerm α) (h : Derivation body Gamma (eqn r (suc t))) :
    Derivation body Gamma (successorExists r) := by
  apply Derivation.existentialIntroduction (emb t)
  simp only [eqnInstantiate,liftBind,sucSubst,varBind]
  exact h

def zeroOrSuccessor (r : OTerm α) : Derivation body Gamma (zeroOrSuccessorFormula r) := by
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let theta := zeroOrSuccessorFormula x
  have hb : Derivation body Gamma (instantiate theta (emb z)) := by
    simp only [theta,x,zeroOrSuccessorInstantiate,varBind]
    exact orLeft (refl z)
  have hs : Derivation body (theta :: Gamma.map weaken) (successorInstance theta) := by
    simp only [theta,successorInstance,nextEmbedding,zeroOrSuccessorSubst,x,varNext]
    exact orRight (successorIntroduction (suc x) x (refl (suc x)))
  have h := Derivation.universalElimination (emb r) (natInduction theta hb hs)
  simpa only [theta,x,zeroOrSuccessorInstantiate,varBind] using h

theorem successorCases (Gamma : List (Formula α)) (r : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (successorExists r)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (t : OTerm β),
      (∀ f ∈ Gamma, f.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (eqn (r.relabel j) (suc t))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  have he := k (α ⊕ Fin 1) Sum.inl
    ((eqn (r.relabel Sum.inl) (suc (.var (.inr 0)))) :: Gamma.map weaken)
    (.var (.inr 0))
    (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨he⟩ := he
  exact ⟨Derivation.existentialElimination h he⟩

theorem actualZeroOrSuccessor : InternalLinearCombinationZeroRemainderTargets.ActualZeroOrSuccessor := by
  intro body α Gamma r
  rw [onEquality,onEquality]
  exact ⟨zeroOrSuccessor r⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationZeroRemainderProof
