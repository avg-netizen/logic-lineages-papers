module

public import LogicLineages.ModelsAlgebra.Differential.CurveDifferentialDefinitions

@[expose] public section

/-! Independent source targets for paper 15, proof of `lem:curve`,
paper.tex lines 143–153 and equation `eq:second`. The chain rule is fully
general. The curve-specific consequences retain only irreducibility,
positive Z-degree, nonconstancy, and the actual equation. Nonvanishing of
the separant, transcendence, and differential closure are conclusions of
proof suppliers, never input assumptions. Actual first-jet and all-jet
field adjoins occur in the type. Written before the external candidate.
These statements do not yet construct the two-root differential isomorphism. -/

namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u

def pairEvaluationChainRule : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (D : Derivation ℤ F F)
    (p : BivariatePolynomial) (a b : F),
    D (pairEval a b p) = pairEval a b (partialY p) * D a +
      pairEval a b (separant p) * D b

def curveSecondJet : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (D : Derivation ℤ F F)
    (p : BivariatePolynomial) (a : F),
    Irreducible p → 0 < p.natDegree → D a ≠ 0 → pairEval a (D a) p = 0 →
    D (D a) = -(pairEval a (D a) (partialY p) * D a) /
      pairEval a (D a) (separant p)

def curveFirstJetField : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (D : Derivation ℤ F F)
    (p : BivariatePolynomial) (a : F),
    Irreducible p → 0 < p.natDegree → D a ≠ 0 → pairEval a (D a) p = 0 →
    IsDerivationClosed (integerDerivationToRat D) (firstJetField D a) ∧
      firstJetField D a = fieldGeneratedByJets (integerDerivationToRat D) a

end LogicLineages.ModelsAlgebra.Differential.Targets
