module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaBoundaryProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof InternalBetaWitness InternalBetaTotality
open InternalBetaWitnessProof InternalBetaDivisionProof InternalBetaBoundaryProof
open InternalBetaDivisionSyntaxProof InternalBetaTotalitySyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalOriginalOrderSyntaxProof InternalAdditionLawsProof InternalMultiplicationLawsProof
open InternalPositiveUnfoldingSupportProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

def addHyp {p : Formula α} (d : Derivation body Gamma p) (q : Formula α) :
    Derivation body (q :: Gamma) p :=
  Derivation.weakening (fun _ h => List.mem_cons_of_mem _ h) d

/-- Derived elimination for the original classical disjunction connective. -/
def disjunctionElimination {p q c : Formula α}
    (h : Derivation body Gamma (p ⊔ q))
    (hp : Derivation body Gamma (p.imp c)) (hq : Derivation body Gamma (q.imp c)) :
    Derivation body Gamma c := by
  apply Derivation.classical
  have hn : Derivation body (c.not :: Gamma) p.not := by
    apply Derivation.implicationIntroduction
    exact Derivation.implicationElimination
      (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
      (Derivation.implicationElimination (addHyp (addHyp hp c.not) p)
        (Derivation.hypothesis List.mem_cons_self))
  have qb := Derivation.implicationElimination (addHyp h c.not) hn
  exact Derivation.implicationElimination (Derivation.hypothesis List.mem_cons_self)
    (Derivation.implicationElimination (addHyp hq c.not) qb)

def remainderIntroduction (a b i r : OrdinaryArithmetic.Term α)
    (d : Derivation body Gamma (betaF a b i r)) :
    Derivation body Gamma (remainderExists a b i) := by
  unfold remainderExists
  apply Derivation.existentialIntroduction (emb r)
  rw [betaInstantiate]
  simp only [liftBind,varBind]
  exact d

theorem remainderCases (Gamma : List (Formula α)) (a b i : OrdinaryArithmetic.Term α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (remainderExists a b i)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (r : OrdinaryArithmetic.Term β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (betaF (a.relabel j) (b.relabel j) (i.relabel j) r)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  have e := k (α ⊕ Fin 1) Sum.inl
    (betaF (a.relabel Sum.inl) (b.relabel Sum.inl) (i.relabel Sum.inl) (.var (.inr 0)) :: Gamma.map weaken)
    (.var (.inr 0)) (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨e⟩ := e
  exact ⟨Derivation.existentialElimination h e⟩

theorem actualBetaSuccessorExistence : InternalBetaTotalityTargets.ActualBetaSuccessorExistence := by
  intro body α a b i r
  let Gamma := [betaF a b i r]
  let p := ltF (suc r) (modulus b i)
  let q := eqn (suc r) (modulus b i)
  let c := remainderExists (suc a) b i
  have hb : Derivation body Gamma (betaF a b i r) := Derivation.hypothesis List.mem_cons_self
  obtain ⟨bound⟩ := InternalBetaDivisionProof.actualBetaRemainderBound body α a b i r
  obtain ⟨split⟩ := InternalBetaBoundaryProof.actualDiscreteOrderBoundary body α r (modulus b i)
  change Derivation body [] ((ltF r (modulus b i)).imp
    (p ⊔ arithmeticEmbedding.onFormula ((suc r).equal (modulus b i)))) at split
  rw [onEquality] at split
  have hd : Derivation body Gamma (p ⊔ q) := Derivation.implicationElimination
    (weakenClosed split Gamma) (Derivation.implicationElimination (weakenClosed bound Gamma) hb)
  have hp : Nonempty (Derivation body Gamma (p.imp c)) := by
    obtain ⟨step⟩ := InternalBetaDivisionProof.actualBetaSuccessorBelowModulus body α a b i r
    exact ⟨Derivation.implicationIntroduction
      (remainderIntroduction (suc a) b i (suc r)
        (Derivation.implicationElimination (weakenClosed step (p :: Gamma))
          (Derivation.conjunctionIntroduction (addHyp hb p) (Derivation.hypothesis List.mem_cons_self))))⟩
  have hq : Nonempty (Derivation body Gamma (q.imp c)) := by
    obtain ⟨step⟩ := InternalBetaBoundaryProof.actualBetaSuccessorAtModulus body α a b i r
    change Derivation body [] ((betaF a b i r ⊓ arithmeticEmbedding.onFormula
      ((suc r).equal (modulus b i))).imp (betaF (suc a) b i z)) at step
    rw [onEquality] at step
    exact ⟨Derivation.implicationIntroduction
      (remainderIntroduction (suc a) b i z
        (Derivation.implicationElimination (weakenClosed step (q :: Gamma))
          (Derivation.conjunctionIntroduction (addHyp hb q) (Derivation.hypothesis List.mem_cons_self))))⟩
  obtain ⟨hp⟩ := hp
  obtain ⟨hq⟩ := hq
  exact ⟨Derivation.implicationIntroduction (disjunctionElimination hd hp hq)⟩

theorem remainderStep (Gamma : List (Formula α)) (a b i : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (remainderExists a b i))) :
    Nonempty (Derivation body Gamma (remainderExists (suc a) b i)) := by
  apply remainderCases Gamma a b i _ h
  intro β j Delta r _ ⟨hβ⟩
  rw [remainderExistsRename,sucRelabel]
  obtain ⟨step⟩ := actualBetaSuccessorExistence body β (a.relabel j) (b.relabel j) (i.relabel j) r
  exact ⟨Derivation.implicationElimination (weakenClosed step Delta) hβ⟩

theorem actualBetaTotality : InternalBetaTotalityTargets.ActualBetaTotality := by
  intro body α a b i
  let x : OrdinaryArithmetic.Term (α ⊕ Fin 1) := .var (.inr 0)
  let theta := remainderExists x (b.relabel Sum.inl) (i.relabel Sum.inl)
  obtain ⟨zero⟩ := actualBetaZero body α b i
  have hb : Derivation body [] (instantiate theta (emb z)) := by
    simp only [theta,x,remainderExistsInstantiate,liftBind,varBind]
    exact remainderIntroduction z b i z zero
  have hs : Nonempty (Derivation body [theta] (successorInstance theta)) := by
    simp only [theta,x,remainderExistsSuccessor,liftNext,varNext]
    apply remainderStep [theta] x (b.relabel Sum.inl) (i.relabel Sum.inl)
    exact ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb a) (natInduction theta hb hs)
  simpa only [theta,x,remainderExistsInstantiate,liftBind,varBind] using (Nonempty.intro h)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
