module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

/-!
Independent fraction-field extension supplier for paper 15,
`lem:genericcurve`, paper.tex lines 169–178: the prescribed derivation
of the coordinate domain may take values in its fraction field because
the separant is inverted. No preservation of the coordinate domain is
assumed. The scalar tower below is the genuine coherence of the given
algebra maps, not an extension/linearity correctness oracle.

The source rational base specializes the stronger arbitrary-field base.
These targets neither prove stability of the curve relation nor construct
the generic solution; those remain separate obligations. Written before
the external candidate. The second target uses the actual FractionRing
construction, not an assumed fraction-field interface.
-/

namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u v w

/-- Extend a fraction-field-valued derivation uniquely to the fraction field. -/
def fractionFieldDerivationExtension : Prop :=
  ∀ (K : Type u) (R : Type v) (F : Type w)
    [Field K] [CommRing R] [IsDomain R] [Field F]
    [Algebra K R] [Algebra K F] [Algebra R F] [IsScalarTower K R F]
    [IsFractionRing R F] (D : Derivation K R F),
    ∃! E : Derivation K F F, ∀ r, E (algebraMap R F r) = D r

/-- Specialization to the actual constructed fraction field. -/
def constructedFractionFieldDerivationExtension : Prop :=
  ∀ (K : Type u) (R : Type v) [Field K] [CommRing R] [IsDomain R]
    [Algebra K R] (D : Derivation K R (FractionRing R)),
    ∃! E : Derivation K (FractionRing R) (FractionRing R),
      ∀ r, E (algebraMap R (FractionRing R) r) = D r

end LogicLineages.ModelsAlgebra.Differential.Targets
