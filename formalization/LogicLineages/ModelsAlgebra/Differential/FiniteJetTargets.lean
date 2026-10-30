module

public import LogicLineages.ModelsAlgebra.Differential.FiniteJetDefinitions

@[expose] public section

/-! Exact finite-recurrence suppliers for paper 15 lem:genericjets. The
algebraic-independence hypotheses here are discharged by the separate
spectral coordinate proof; ordinary splitting transport and rational R_f
nonvanishing remain explicit full-source obligations. -/
namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u v

def finiteJetClosedAndEqualsGenerated : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (D : Derivation ℚ F F)
    (a : F) (n : ℕ) (c : Fin n → ℚ), 0 < n → FiniteJet.Recurrence D a n c →
    IsDerivationClosed D (FiniteJet.field D a n) ∧
      FiniteJet.field D a n = fieldGeneratedByJets D a

def independentFiniteJetIsomorphism : Prop :=
  ∀ (F : Type u) (H : Type v) [Field F] [CharZero F] [Field H] [CharZero H]
    (D : Derivation ℤ F F) (E : Derivation ℤ H H)
    (a : F) (b : H) (n : ℕ) (c : Fin n → ℚ), 0 < n →
    FiniteJet.Recurrence (integerDerivationToRat D) a n c →
    FiniteJet.Recurrence (integerDerivationToRat E) b n c →
    AlgebraicIndependent ℚ (FiniteJet.family (integerDerivationToRat D) a n) →
    AlgebraicIndependent ℚ (FiniteJet.family (integerDerivationToRat E) b n) →
    HasDesignatedRootIso D E a b

end LogicLineages.ModelsAlgebra.Differential.Targets
