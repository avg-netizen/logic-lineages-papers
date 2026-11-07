module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOrientedBezoutTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationCommutativityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBezoutCRTProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientGapProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOrientedBezoutArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalSourceInversionSupportProof InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalAdditionCancellationProof InternalMultiplicationLawsProof
open InternalMultiplicationCommutativityProof InternalQuotientGapProof InternalBezoutCRTProof
open InternalOrientedBezout (leftCoefficient rightCoefficient)
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

def productSwap (x a b : OTerm α) :
    Derivation body Gamma (eqn (mul (mul x a) b) (mul (mul x b) a)) :=
  trans (multiplicationAssociativity x a b)
    (trans (congMulLeft x (multiplicationCommutativity a b))
      (symm (multiplicationAssociativity x b a)))

def fourSwap (a b c d : OTerm α) :
    Derivation body Gamma (eqn (add (add a b) (add c d)) (add (add a d) (add b c))) :=
  trans (symm (associativity (add a b) c d))
    (trans (swapMiddle (add a b) c d)
      (trans (congAddRight c (swapMiddle a b d)) (associativity (add a d) b c)))

def conversion (a b x y z' w : OTerm α)
    (h : Derivation body Gamma
      (eqn (add (mul x (suc a)) (mul y (suc b)))
        (add one (add (mul z' (suc a)) (mul w (suc b)))))) :
    Derivation body Gamma
      (eqn (suc (mul (leftCoefficient b x z' w) (suc a)))
        (mul (rightCoefficient a x y w) (suc b))) := by
  let A := suc a
  let B := suc b
  let X := mul x A
  let Y := mul y B
  let Z := mul z' A
  let W := mul w B
  let P := mul (mul x A) b
  let T := mul (mul w a) B
  have hw : Derivation body Gamma (eqn (mul (mul w B) A) (add T W)) :=
    trans (productSwap w B A)
      (trans (congMulRight B (mulSucc w a)) (leftDistributivity (mul w a) w B))
  have hl : Derivation body Gamma
      (eqn (mul (leftCoefficient b x z' w) A) (add (add Z W) (add P T))) :=
    trans (leftDistributivity (add z' (mul x b)) (mul w B) A)
      (trans (congAddRight (mul (mul w B) A) (leftDistributivity z' (mul x b) A))
        (trans (congAddRight (mul (mul w B) A) (congAddLeft Z (productSwap x b A)))
          (trans (congAddLeft (add Z P) hw) (fourSwap Z P T W))))
  have hr : Derivation body Gamma
      (eqn (mul (rightCoefficient a x y w) B) (add (add X Y) (add P T))) :=
    trans (leftDistributivity (add (mul x A) y) (mul w a) B)
      (trans (congAddRight T (leftDistributivity (mul x A) y B))
        (trans (congAddRight T (congAddRight Y (mulSucc (mul x A) b)))
          (trans (congAddRight T (congAddRight Y (commutativity P X)))
            (trans (congAddRight T (swapMiddle X P Y)) (associativity (add X Y) P T)))))
  exact trans (congSuc hl)
    (trans (symm (oneAdd (add (add Z W) (add P T))))
      (trans (symm (associativity one (add Z W) (add P T)))
        (trans (congAddRight (add P T) (symm h)) (symm hr))))

theorem actualSignedConversion : InternalOrientedBezoutTargets.ActualSignedConversion := by
  intro body α a b x y z' w
  unfold InternalLinearCombination.equation InternalBezoutCRT.certificate
  rw [onEquality,onEquality]
  exact ⟨Derivation.implicationIntroduction
    (conversion a b x y z' w (Derivation.hypothesis List.mem_cons_self))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOrientedBezoutArithmeticProof
