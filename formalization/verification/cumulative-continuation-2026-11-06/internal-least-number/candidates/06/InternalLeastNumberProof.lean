module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalAdditionLawsProof
open InternalBetaBoundaryProof InternalQuotientComparisonProof InternalLeastNumberSyntaxProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Induction on the original additive witness, in the object calculus. -/
def additiveBoundary (s t d : OTerm α) :
    Derivation body Gamma ((eqn (add s d) t).imp (ltF s t ⊔ eqn s t)) := by
  let a := s.relabel (Sum.inl : α → α ⊕ Fin 1)
  let b := t.relabel (Sum.inl : α → α ⊕ Fin 1)
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let psi := ltF s t ⊔ eqn s t
  let theta := (eqn (add a x) b).imp (weaken psi)
  have hb : Derivation body Gamma (instantiate theta (emb z)) := by
    simp only [theta,a,b,x,impInstantiate,eqnInstantiate,addSubst,liftBind,varBind,instantiateWeaken]
    apply Derivation.implicationIntroduction
    exact orRight (trans (symm (addZero s)) (Derivation.hypothesis List.mem_cons_self))
  have hs : Derivation body (theta :: Gamma.map weaken) (successorInstance theta) := by
    simp only [theta,a,b,x,successorInstance,nextEmbedding,impSubst,eqnSubst,addSubst,liftNext,varNext,nextWeaken]
    change Derivation body (theta :: Gamma.map weaken)
      ((eqn (add a (suc x)) b).imp ((ltF s t ⊔ eqn s t).relabel Sum.inl))
    rw [supRename,orderRename,eqnRelabel]
    apply Derivation.implicationIntroduction
    apply orLeft
    rw [embedding]
    apply Derivation.existentialIntroduction (emb x)
    rw [witnessInstantiate]
    exact Derivation.hypothesis List.mem_cons_self
  have h := Derivation.universalElimination (emb d) (natInduction theta hb hs)
  simpa only [theta,a,b,x,impInstantiate,eqnInstantiate,addSubst,liftBind,varBind,instantiateWeaken] using h

theorem actualRightSuccessorSplit : InternalLeastNumberTargets.ActualRightSuccessorSplit := by
  intro body α s t
  have h : Nonempty (Derivation body [ltF s (suc t)] (ltF s t ⊔ eqn s t)) := by
    apply orderCases [ltF s (suc t)] s (suc t) _ ⟨Derivation.hypothesis List.mem_cons_self⟩
    intro β j Delta d _ ⟨e⟩
    rw [supRename,orderRename,eqnRelabel]
    simp only [sucRelabel] at e
    exact ⟨Derivation.implicationElimination (additiveBoundary (s.relabel j) (t.relabel j) d)
      (cancelSuc (trans (symm (addSucc (s.relabel j) d)) e))⟩
  obtain ⟨h⟩ := h
  change Nonempty (Derivation body [] ((ltF s (suc t)).imp
    (ltF s t ⊔ arithmeticEmbedding.onFormula (s.equal t))))
  rw [onEquality]
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualNothingBelowZero : InternalLeastNumberTargets.ActualNothingBelowZero := by
  intro body α s
  have h : Nonempty (Derivation body [ltF s z] (⊥ : Formula α)) := by
    apply orderCases [ltF s z] s z _ ⟨Derivation.hypothesis List.mem_cons_self⟩
    intro β j Delta d _ ⟨e⟩
    simp only [zRelabel] at e
    exact ⟨Derivation.implicationElimination (sucNeZero (add (s.relabel j) d))
      (trans (symm (addSucc (s.relabel j) d)) e)⟩
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationIntroduction h⟩

open InternalDerivationRenamingProof InternalDerivationRenamingSyntaxProof
open InternalPositiveUnfoldingSupportProof InternalBinderTransportProof InternalBetaTotalityProof

theorem belowZero (p : Formula (α ⊕ Fin 1)) :
    Nonempty (Derivation body Gamma (below p z)) := by
  obtain ⟨hz⟩ := actualNothingBelowZero body (α ⊕ Fin 1) (.var (.inr 0))
  apply Nonempty.intro
  apply Derivation.universalIntroduction
  simp only [zRelabel]
  apply Derivation.implicationIntroduction
  exact Derivation.explosion (Derivation.implicationElimination
    (weakenClosed hz _) (Derivation.hypothesis List.mem_cons_self))

def excludeAt (p : Formula (α ⊕ Fin 1)) (t : OTerm α)
    (hn : Derivation body Gamma (existsOne (minP p)).not)
    (hb : Derivation body Gamma (below p t)) :
    Derivation body Gamma (instantiate p (emb t)).not := by
  apply Derivation.implicationIntroduction
  apply Derivation.implicationElimination (addHyp hn _)
  apply Derivation.existentialIntroduction (emb t)
  rw [minInstantiate]
  exact Derivation.conjunctionIntroduction (Derivation.hypothesis List.mem_cons_self) (addHyp hb _)

theorem belowStep (p : Formula (α ⊕ Fin 1)) (t : OTerm α)
    (hb : Nonempty (Derivation body Gamma (below p t)))
    (hn : Nonempty (Derivation body Gamma (instantiate p (emb t)).not)) :
    Nonempty (Derivation body Gamma (below p (suc t))) := by
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let w := t.relabel (Sum.inl : α → α ⊕ Fin 1)
  let Delta := (ltF x (suc w)) :: Gamma.map weaken
  have hi : ∀ q ∈ Gamma, q.relabel Sum.inl ∈ Delta := by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have hb' := renameInto hb Sum.inl Delta hi
  rw [belowRename] at hb'
  obtain ⟨hb'⟩ := hb'
  have hn' := renameInto hn Sum.inl Delta hi
  change Nonempty (Derivation body Delta ((instantiate p (emb t)).relabel Sum.inl).not) at hn'
  rw [instantiateRename] at hn'
  obtain ⟨hn'⟩ := hn'
  obtain ⟨split⟩ := actualRightSuccessorSplit body (α ⊕ Fin 1) x w
  change Derivation body [] ((ltF x (suc w)).imp (ltF x w ⊔ arithmeticEmbedding.onFormula (x.equal w))) at split
  rw [onEquality] at split
  have hd : Derivation body Delta (ltF x w ⊔ eqn x w) :=
    Derivation.implicationElimination (weakenClosed split Delta) (Derivation.hypothesis List.mem_cons_self)
  have hl : Derivation body Delta ((ltF x w).imp p.not) := by
    have hh := Derivation.universalElimination (emb x) hb'
    rw [belowElimSyntax] at hh
    change Derivation body Delta ((ltF x w).imp (instantiate (liftP p) (emb x)).not) at hh
    simpa only [x,freshP] using hh
  have hr : Derivation body Delta ((eqn x w).imp p.not) := by
    apply Derivation.implicationIntroduction
    apply Derivation.implicationIntroduction
    have he : Derivation body (p :: eqn x w :: Delta) (eqn x w) :=
      Derivation.hypothesis (by simp)
    have hp : Derivation body (p :: eqn x w :: Delta) (instantiate (liftP p) (emb x)) := by
      rw [show x = .var (.inr 0) from rfl,freshP]
      exact Derivation.hypothesis List.mem_cons_self
    have hh := Derivation.equalityElimination (liftP p) (emb x) (emb w) he hp
    exact Derivation.implicationElimination (addHyp (addHyp hn' (eqn x w)) p) hh
  have h := disjunctionElimination hd hl hr
  apply Nonempty.intro
  apply Derivation.universalIntroduction
  change Derivation body (Gamma.map weaken) ((ltF x (suc w)).imp p.not)
  exact Derivation.implicationIntroduction h

theorem exclusionCourse (p : Formula (α ⊕ Fin 1)) :
    Nonempty (Derivation body [(existsOne (minP p)).not] (course p)) := by
  let Gamma := [(existsOne (minP p)).not]
  let theta := below (liftP p) (.var (.inr 0))
  have hb : Nonempty (Derivation body Gamma (instantiate theta (emb z))) := by
    rw [show theta = below (liftP p) (.var (.inr 0)) from rfl,belowInstantiate]
    exact belowZero p
  have hs : Nonempty (Derivation body (theta :: Gamma.map weaken) (successorInstance theta)) := by
    rw [show theta = below (liftP p) (.var (.inr 0)) from rfl,belowSuccessor]
    have hn : Derivation body (theta :: Gamma.map weaken) (existsOne (minP (liftP p))).not := by
      have he := Derivation.hypothesis (body := body) (Gamma := theta :: Gamma.map weaken)
        (phi := weaken (existsOne (minP p)).not) (by simp [Gamma])
      change Derivation body _ (((existsOne (minP p)).not).relabel Sum.inl) at he
      rw [noMinRename] at he
      exact he
    have hi : Derivation body (theta :: Gamma.map weaken) (below (liftP p) (.var (.inr 0))) :=
      Derivation.hypothesis List.mem_cons_self
    exact belowStep (liftP p) (.var (.inr 0)) ⟨hi⟩ ⟨excludeAt (liftP p) (.var (.inr 0)) hn hi⟩
  obtain ⟨hb⟩ := hb
  obtain ⟨hs⟩ := hs
  exact ⟨natInduction theta hb hs⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberProof
