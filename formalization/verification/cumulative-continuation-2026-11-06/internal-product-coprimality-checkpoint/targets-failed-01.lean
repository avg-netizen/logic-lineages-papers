module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOrientedBezoutTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalProductCoprimalityTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalBezoutExistenceTargets
/-- Object-calculus multiplication of oriented unit certificates, arbitrary terms. -/
def ActualCertificateProduct : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (m a b u v w z : OTerm α),
  Nonempty (Derivation body [] ((eqn (suc (mul u m)) (mul v a) ⊓
    eqn (suc (mul w m)) (mul z b)).imp
    (eqn (suc (mul (add (add u w) (mul (mul u w) m)) m))
      (mul (mul v z) (mul a b)))))
/-- Actual positive-common-divisor formula, not a certificate predicate. -/
def ActualPositiveProductCoprimality : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (m a b : OTerm α),
  Nonempty (Derivation body [] ((coprime (suc m) (suc a) ⊓
    coprime (suc m) (suc b)).imp (coprime (suc m) (mul (suc a) (suc b)))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalProductCoprimalityTargets
