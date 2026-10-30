module

public import LogicLineages.ModelsAlgebra.Differential.FiniteJetDefinitions

@[expose] public section

/-! Literal designated-root differential isomorphisms preserve all rational
polynomial relations among jets. This is the separation argument in the
negative branch of paper 15 thm:spectral; no relation-preservation oracle is
built into HasDesignatedRootIso. -/
namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u v

def designatedRootIsoPreservesJetRelations : Prop :=
  ∀ (F : Type u) (H : Type v) [Field F] [CharZero F] [Field H] [CharZero H]
    (D : Derivation ℤ F F) (E : Derivation ℤ H H) (a : F) (b : H),
    HasDesignatedRootIso D E a b →
    ∀ (n : ℕ) (q : MvPolynomial (Fin n) ℚ),
      MvPolynomial.aeval (FiniteJet.family (integerDerivationToRat D) a n) q = 0 ↔
      MvPolynomial.aeval (FiniteJet.family (integerDerivationToRat E) b n) q = 0

end LogicLineages.ModelsAlgebra.Differential.Targets
