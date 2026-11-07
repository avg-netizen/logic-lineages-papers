module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientGapTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLeftSuccessorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientGapProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof InternalSourceInversionSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalAdditionCancellationProof InternalMultiplicationLawsProof
open InternalMultiplicationLeftSuccessorProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

def congMulRight (u : OTerm α) {s t : OTerm α} (d : Derivation body Gamma (eqn s t)) :
    Derivation body Gamma (eqn (mul s u) (mul t u)) := by
  have h := congTerm (mul (.var (.inr (0 : Fin 1))) (u.relabel Sum.inl)) d
  simpa only [mulSubst,liftBind,varBind] using h

def swapMiddle (a b c : OTerm α) :
    Derivation body Gamma (eqn (add (add a b) c) (add (add a c) b)) :=
  trans (associativity a b c)
    (trans (congAddLeft a (commutativity b c)) (symm (associativity a c b)))

def leftDistributivity (s t u : OTerm α) :
    Derivation body Gamma (eqn (mul (add s t) u) (add (mul s u) (mul t u))) := by
  let a := s.relabel (Sum.inl : α → α ⊕ Fin 1)
  let b := t.relabel (Sum.inl : α → α ⊕ Fin 1)
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let theta := eqn (mul (add a b) x) (add (mul a x) (mul b x))
  have hb : Derivation body Gamma (instantiate theta (emb z)) := by
    simp only [theta,a,b,x,eqnInstantiate,mulSubst,addSubst,liftBind,varBind]
    exact trans (mulZero (add s t)) (symm
      (trans (congAddRight (mul t z) (mulZero s))
        (trans (leftZero (mul t z)) (mulZero t))))
  have hs : Derivation body (theta :: Gamma.map weaken) (successorInstance theta) := by
    simp only [theta,a,b,x,successorInstance,nextEmbedding,eqnSubst,mulSubst,addSubst,liftNext,varNext]
    have rearrange : Derivation body (theta :: Gamma.map weaken)
        (eqn (add (add (mul a x) (mul b x)) (add a b))
          (add (add (mul a x) a) (add (mul b x) b))) :=
      trans (symm (associativity (add (mul a x) (mul b x)) a b))
        (trans (congAddRight b (swapMiddle (mul a x) (mul b x) a))
          (associativity (add (mul a x) a) (mul b x) b))
    exact trans (mulSucc (add a b) x)
      (trans (congAddRight (add a b) (Derivation.hypothesis List.mem_cons_self))
        (trans rearrange (symm
          (trans (congAddRight (mul b (suc x)) (mulSucc a x))
            (congAddLeft (add (mul a x) a) (mulSucc b x))))))
  have h := Derivation.universalElimination (emb u) (natInduction theta hb hs)
  simpa only [theta,a,b,x,eqnInstantiate,mulSubst,addSubst,liftBind,varBind] using h

def gapContradiction (a M q q' r s d w : OTerm α)
    (ha : Derivation body Gamma (eqn a (add (mul q M) r)))
    (ha' : Derivation body Gamma (eqn a (add (mul q' M) s)))
    (hr : Derivation body Gamma (eqn (add r (suc d)) M))
    (hq : Derivation body Gamma (eqn (add q (suc w)) q')) :
    Derivation body Gamma ⊥ := by
  let Q := mul q M
  let W := mul w M
  have hp : Derivation body Gamma (eqn (mul q' M) (add Q (add W M))) :=
    trans (congMulRight M (symm hq))
      (trans (leftDistributivity q (suc w) M)
        (congAddLeft Q (leftSuccessorMultiplication w M)))
  have hi : Derivation body Gamma
      (eqn (add W M) (add r (suc (add W d)))) :=
    trans (congAddLeft W (symm hr))
      (trans (symm (associativity W r (suc d)))
        (trans (congAddRight (suc d) (commutativity W r))
          (trans (associativity r W (suc d))
            (congAddLeft r (addSucc W d)))))
  have hj : Derivation body Gamma
      (eqn (add (mul q' M) s) (add (add Q r) (suc (add (add W d) s)))) :=
    trans (congAddRight s hp)
      (trans (congAddRight s (congAddLeft Q hi))
        (trans (congAddRight s (symm (associativity Q r (suc (add W d)))))
          (trans (associativity (add Q r) (suc (add W d)) s)
            (congAddLeft (add Q r) (leftSuccessor (add W d) s)))))
  exact Derivation.implicationElimination
    (InternalOriginalOrderProof.noLoop (add Q r) (add (add W d) s))
    (trans (symm hj) (trans (symm ha') ha))

theorem actualLeftDistributivity : InternalQuotientGapTargets.ActualLeftDistributivity := by
  intro body α Gamma s t u
  rw [onEquality]
  exact ⟨leftDistributivity s t u⟩
theorem actualQuotientGapContradiction : InternalQuotientGapTargets.ActualQuotientGapContradiction := by
  intro body α Gamma a M q q' r s d w ha ha' hr hq
  simp only [onEquality] at ha ha' hr hq
  exact ⟨gapContradiction a M q q' r s d w ha ha' hr hq⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientGapProof
