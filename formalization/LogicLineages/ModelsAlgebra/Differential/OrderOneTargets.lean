module

public import LogicLineages.ModelsAlgebra.Differential.ConstrainedDefinitions
public import LogicLineages.ModelsAlgebra.Differential.RadicalDefinitions

@[expose] public section

/-! Independent exact comparators for paper 15 thm:orderone (lines 114–128,
proof 186–209). These are semantic criteria, not the algorithmic corollary.
The actual small witnesses must be transported to every universe; the three
ULift obligations explicitly check derivative, polynomial, and jet transport.
No field witness, separant, nonconstancy, or isomorphism oracle is assumed.
Written before the criterion candidate. -/
namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u v

def liftedOrdinaryDerivation : Prop :=
  ∀ (F : Type v) [Field F] (D : Derivation ℤ F F) (x : ULift.{u} F),
    (liftOrdinaryDerivation D x).down = D x.down

def liftedPolynomialEvaluation : Prop :=
  ∀ (F : Type v) [Field F] [CharZero F] (a b : F)
    (p : BivariatePolynomial) (q : Polynomial ℚ),
    (pairEval (ULift.up a : ULift.{u} F) (ULift.up b) p).down = pairEval a b p ∧
    (Polynomial.aeval (ULift.up a : ULift.{u} F) q).down = Polynomial.aeval a q

def liftedJetEvaluation : Prop :=
  ∀ (F : Type v) [Field F] [CharZero F] (D : Derivation ℤ F F) (a : F) (n : ℕ),
    jet (integerDerivationToRat (liftOrdinaryDerivation D)) (ULift.up a : ULift.{u} F) n =
      ULift.up (jet (integerDerivationToRat D) a n)

def orderOneNonzeroSpecialization : Prop :=
  ∀ (p : BivariatePolynomial) (q : Polynomial ℚ),
    Irreducible p → 0 < p.natDegree → q ≠ 0 → p.eval 0 ≠ 0 →
    (ConstrainedOrderOne.{u} p q ↔ rationalRadical (p.eval 0) ∣ q)

def orderOneZeroSpecialization : Prop :=
  ∀ (p : BivariatePolynomial) (q : Polynomial ℚ),
    Irreducible p → 0 < p.natDegree → q ≠ 0 → p.eval 0 = 0 →
    ¬ConstrainedOrderOne.{u} p q

def orderOneCriterion : Prop :=
  ∀ (p : BivariatePolynomial) (q : Polynomial ℚ),
    Irreducible p → 0 < p.natDegree → q ≠ 0 →
    (ConstrainedOrderOne.{u} p q ↔ p.eval 0 ≠ 0 ∧ rationalRadical (p.eval 0) ∣ q)

end LogicLineages.ModelsAlgebra.Differential.Targets
