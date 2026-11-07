module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalProductCoprimalityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOrientedBezoutArithmeticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalProductCoprimalityArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalMultiplicationLawsProof InternalMultiplicationCommutativityProof
open InternalQuotientGapProof InternalOrientedBezoutArithmeticProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
def shuffleProduct (a b c d : OTerm α) :
    Derivation body Gamma (eqn (mul (mul a b) (mul c d)) (mul (mul a c) (mul b d))) :=
  trans (symm (multiplicationAssociativity (mul a b) c d))
    (trans (congMulRight d (productSwap a b c)) (multiplicationAssociativity (mul a c) b d))
def successorProduct (U W : OTerm α) :
    Derivation body Gamma (eqn (mul (suc U) (suc W))
      (suc (add (add U W) (mul U W)))) := by
  have h : Derivation body Gamma (eqn (mul (suc U) W) (add (mul U W) W)) :=
    trans (multiplicationCommutativity (suc U) W)
      (trans (mulSucc W U) (congAddRight W (multiplicationCommutativity W U)))
  exact trans (mulSucc (suc U) W)
    (trans (congAddRight (suc U) h)
      (trans (addSucc (add (mul U W) W) U)
        (congSuc (trans (commutativity (add (mul U W) W) U)
          (trans (congAddLeft U (commutativity (mul U W) W))
            (symm (associativity U W (mul U W))))))))
def certificateProduct (m a b u v w z' : OTerm α)
    (h : Derivation body Gamma (eqn (suc (mul u m)) (mul v a)))
    (k : Derivation body Gamma (eqn (suc (mul w m)) (mul z' b))) :
    Derivation body Gamma
      (eqn (suc (mul (add (add u w) (mul (mul u w) m)) m))
        (mul (mul v z') (mul a b))) := by
  have hc : Derivation body Gamma
      (eqn (mul (add (add u w) (mul (mul u w) m)) m)
        (add (add (mul u m) (mul w m)) (mul (mul u m) (mul w m)))) :=
    trans (leftDistributivity (add u w) (mul (mul u w) m) m)
      (trans (congAddRight (mul (mul (mul u w) m) m) (leftDistributivity u w m))
        (congAddLeft (add (mul u m) (mul w m))
          (trans (multiplicationAssociativity (mul u w) m m) (shuffleProduct u w m m))))
  exact trans (congSuc hc)
    (trans (symm (successorProduct (mul u m) (mul w m)))
      (trans (congMulRight (suc (mul w m)) h)
        (trans (congMulLeft (mul v a) k) (shuffleProduct v a z' b))))
theorem actualCertificateProduct : InternalProductCoprimalityTargets.ActualCertificateProduct := by
  intro body α m a b u v w z'
  have h := Derivation.hypothesis (body := body)
    (List.mem_cons_self (a := eqn (suc (mul u m)) (mul v a) ⊓ eqn (suc (mul w m)) (mul z' b)) (l := []))
  exact ⟨Derivation.implicationIntroduction
    (certificateProduct m a b u v w z' (Derivation.conjunctionLeft h) (Derivation.conjunctionRight h))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalProductCoprimalityArithmeticProof
