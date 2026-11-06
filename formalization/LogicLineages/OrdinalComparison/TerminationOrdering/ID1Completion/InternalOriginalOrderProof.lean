module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalAdditionLawsProof InternalOriginalOrderSyntaxProof InternalDerivationRenamingProof

theorem actualOriginalOrderIntroduction : InternalOriginalOrderTargets.ActualOriginalOrderIntroduction := by
  intro body α Gamma s t w ⟨d⟩
  rw [onEquality] at d
  change Nonempty (Derivation body Gamma (ltF s t))
  rw [embedding]
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb w)
  rw [witnessInstantiate]
  exact d

theorem actualOriginalOrderElimination : InternalOriginalOrderTargets.ActualOriginalOrderElimination := by
  intro body α Gamma s t psi h e
  rw [actualOriginalOrderEmbedding] at h
  obtain ⟨d⟩ := h
  obtain ⟨e⟩ := e
  exact ⟨Derivation.existentialElimination d e⟩

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Original PA induction excludes an additive strict self-loop. -/
def noLoop (t w : OTerm α) : Derivation body Gamma (eqn (add t (suc w)) t).not := by
  let a := w.relabel (Sum.inl : α → α ⊕ Fin 1)
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let theta := (eqn (add x (suc a)) x).not
  have hb : Derivation body Gamma (instantiate theta (emb z)) := by
    simp only [theta,a,x,notInstantiate,eqnInstantiate,addSubst,sucSubst,liftBind,varBind]
    apply Derivation.implicationIntroduction
    exact Derivation.implicationElimination (sucNeZero w)
      (trans (symm (leftZero (suc w))) (Derivation.hypothesis List.mem_cons_self))
  have hs : Derivation body (theta :: Gamma.map weaken) (successorInstance theta) := by
    simp only [theta,a,x,successorInstance,nextEmbedding,notSubst,eqnSubst,addSubst,sucSubst,liftNext,varNext]
    apply Derivation.implicationIntroduction
    apply Derivation.implicationElimination (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
    exact cancelSuc (trans (symm (leftSuccessor x (suc a))) (Derivation.hypothesis List.mem_cons_self))
  have h := Derivation.universalElimination (emb t) (natInduction theta hb hs)
  simp only [theta,a,x,notInstantiate,eqnInstantiate,addSubst,sucSubst,liftBind,varBind] at h
  exact h

def congAddRight (u : OTerm α) {s t : OTerm α} (d : Derivation body Gamma (eqn s t)) :
    Derivation body Gamma (eqn (add s u) (add t u)) := by
  have h := congTerm (add (.var (.inr (0 : Fin 1))) (u.relabel Sum.inl)) d
  simp only [addSubst,liftBind,varBind] at h
  exact h

/-- The concrete transitivity witness is a+succ(b). -/
def chainWitness (s t u a b : OTerm α)
    (d : Derivation body Gamma (eqn (add s (suc a)) t))
    (e : Derivation body Gamma (eqn (add t (suc b)) u)) :
    Derivation body Gamma (eqn (add s (suc (add a (suc b)))) u) :=
  trans (symm (trans (associativity s (suc a) (suc b))
    (congAddLeft s (leftSuccessor a (suc b)))))
    (trans (congAddRight (suc b) d) e)

theorem renameInto {β : Type} {phi : Formula α} (h : Nonempty (Derivation body Gamma phi))
    (f : α → β) (Delta : List (Formula β)) (hi : ∀ p ∈ Gamma, p.relabel f ∈ Delta) :
    Nonempty (Derivation body Delta (phi.relabel f)) := by
  obtain ⟨d⟩ := h
  obtain ⟨e⟩ := renameDerivation d β f
  apply Nonempty.intro
  apply Derivation.weakening ?_ e
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact hi q hq

theorem orderCases (Gamma : List (Formula α)) (s t : OTerm α) (psi : Formula α)
    (d : Nonempty (Derivation body Gamma (ltF s t)))
    (h : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (w : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (eqn (add (s.relabel j) (suc w)) (t.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) : Nonempty (Derivation body Gamma psi) := by
  rw [embedding] at d
  obtain ⟨d⟩ := d
  let Delta := witnessBody s t :: Gamma.map weaken
  have he : Nonempty (Derivation body Delta (weaken psi)) := by
    apply h (α ⊕ Fin 1) Sum.inl Delta (.var (.inr (0 : Fin 1)))
    · intro p hp
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
    · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨e⟩ := he
  exact ⟨Derivation.existentialElimination d e⟩

theorem actualOriginalOrderIrreflexivity : InternalOriginalOrderTargets.ActualOriginalOrderIrreflexivity := by
  intro body α t
  have h : Nonempty (Derivation body [ltF t t] (⊥ : Formula α)) := by
    apply orderCases [ltF t t] t t _ ⟨Derivation.hypothesis List.mem_cons_self⟩
    intro β j Delta w _ ⟨e⟩
    exact ⟨Derivation.implicationElimination (noLoop (t.relabel j) w) e⟩
  obtain ⟨d⟩ := h
  exact ⟨Derivation.implicationIntroduction d⟩

theorem actualOriginalOrderTransitivity : InternalOriginalOrderTargets.ActualOriginalOrderTransitivity := by
  intro body α s t u
  let Gamma := [ltF s t ⊓ ltF t u]
  have d : Nonempty (Derivation body Gamma (ltF s t)) :=
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
  have e : Nonempty (Derivation body Gamma (ltF t u)) :=
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  have h : Nonempty (Derivation body Gamma (ltF s u)) := by
    apply orderCases Gamma s t _ d
    intro β j Delta a hi da
    rw [orderRename]
    have e' := renameInto e j Delta hi
    rw [orderRename] at e'
    apply orderCases Delta (t.relabel j) (u.relabel j) _ e'
    intro γ l Theta b hl db
    rw [orderRename]
    have da' := renameInto da l Theta hl
    simp only [eqnRelabel,addRelabel,sucRelabel] at da'
    obtain ⟨da'⟩ := da'
    obtain ⟨db⟩ := db
    apply actualOriginalOrderIntroduction body γ Theta ((s.relabel j).relabel l)
      ((u.relabel j).relabel l) (add (a.relabel l) (suc b))
    rw [onEquality]
    exact ⟨chainWitness _ _ _ _ _ da' db⟩
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
