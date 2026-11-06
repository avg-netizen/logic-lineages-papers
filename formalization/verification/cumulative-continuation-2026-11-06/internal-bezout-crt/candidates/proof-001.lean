module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBezoutCRTTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalModularArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLeftSuccessorProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBezoutCRTProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalSourceInversionSupportProof InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalAdditionCancellationProof InternalMultiplicationLawsProof
open InternalMultiplicationLeftSuccessorProof InternalModularArithmeticProof
open InternalBezoutCRT (certificate combine)

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
abbrev one : OrdinaryArithmetic.Term α := suc z

def mulOneRight (t : OrdinaryArithmetic.Term α) : Derivation body Gamma (eqn (mul t one) t) :=
  trans (mulSucc t z) (trans (congAddRight t (mulZero t)) (leftZero t))
def mulOneLeft (t : OrdinaryArithmetic.Term α) : Derivation body Gamma (eqn (mul one t) t) :=
  trans (leftSuccessorMultiplication z t)
    (trans (congAddRight t (multiplicationLeftZero t)) (leftZero t))
def oneAdd (t : OrdinaryArithmetic.Term α) : Derivation body Gamma (eqn (add one t) (suc t)) :=
  trans (leftSuccessor z t) (congSuc (leftZero t))
def addOffsetZero (t m : OrdinaryArithmetic.Term α) :
    Derivation body Gamma (eqn (add t (mul z m)) t) :=
  trans (congAddLeft t (multiplicationLeftZero m)) (addZero t)

theorem equalityCongruence (a b m : OrdinaryArithmetic.Term α) (h : Derivation body Gamma (eqn a b)) :
    Nonempty (Derivation body Gamma (cf a b m)) := by
  apply actualIntroduction body α Gamma a b m z z
  rw [equationEmbedding]
  exact ⟨trans (addOffsetZero a m) (trans h (symm (addOffsetZero b m)))⟩

theorem multipleZero (q m : OrdinaryArithmetic.Term α) :
    Nonempty (Derivation body Gamma (cf (mul q m) z m)) := by
  apply actualIntroduction body α Gamma _ _ _ z q
  rw [equationEmbedding]
  exact ⟨trans (addOffsetZero (mul q m) m) (symm (leftZero (mul q m)))⟩

theorem actualCombination : InternalBezoutCRTTargets.ActualCombination := by
  intro body α Gamma a n u v r s h
  change Nonempty (Derivation body Gamma (eqn (suc (mul u a)) (mul v (suc n)))) at h
  obtain ⟨h⟩ := h
  have ea : Nonempty (Derivation body Gamma (cf (suc (mul u a)) one a)) := by
    apply actualIntroduction body α Gamma _ _ _ z u
    rw [equationEmbedding]
    exact ⟨trans (addOffsetZero _ a) (symm (oneAdd (mul u a)))⟩
  have fa : Nonempty (Derivation body Gamma (cf (mul n (mul u a)) z a)) :=
    actualTransitivity body α Gamma _ _ _ a
      (equalityCongruence _ _ _ (symm (multiplicationAssociativity n u a))) (multipleZero (mul n u) a)
  have eb : Nonempty (Derivation body Gamma (cf (suc (mul u a)) z (suc n))) :=
    actualTransitivity body α Gamma _ _ _ (suc n) (equalityCongruence _ _ _ h) (multipleZero v (suc n))
  have fb : Nonempty (Derivation body Gamma (cf (mul n (mul u a)) one (suc n))) := by
    apply actualIntroduction body α Gamma _ _ _ one (mul n v)
    rw [equationEmbedding]
    exact ⟨trans (congAddLeft _ (mulOneLeft (suc n)))
      (trans (addSucc (mul n (mul u a)) n)
        (trans (congSuc (symm (mulSucc n (mul u a))))
          (trans (congSuc (congMulLeft n h))
            (trans (congSuc (symm (multiplicationAssociativity n v (suc n))))
              (symm (oneAdd (mul (mul n v) (suc n))))))))⟩
  have ca := actualAddition body α Gamma _ _ _ _ a
    (actualMultiplication body α Gamma _ _ a r ea)
    (actualMultiplication body α Gamma _ _ a s fa)
  have cb := actualAddition body α Gamma _ _ _ _ (suc n)
    (actualMultiplication body α Gamma _ _ (suc n) r eb)
    (actualMultiplication body α Gamma _ _ (suc n) s fb)
  have ra : Derivation body Gamma (eqn (add (mul r one) (mul s z)) r) :=
    trans (congAddRight _ (mulOneRight r)) (trans (congAddLeft r (mulZero s)) (addZero r))
  have rb : Derivation body Gamma (eqn (add (mul r z) (mul s one)) s) :=
    trans (congAddRight _ (mulZero r)) (trans (congAddLeft z (mulOneRight s)) (leftZero s))
  obtain ⟨ca⟩ := actualTransitivity body α Gamma _ _ r a ca (equalityCongruence _ _ _ ra)
  obtain ⟨cb⟩ := actualTransitivity body α Gamma _ _ s (suc n) cb (equalityCongruence _ _ _ rb)
  exact ⟨Derivation.conjunctionIntroduction ca cb⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBezoutCRTProof
