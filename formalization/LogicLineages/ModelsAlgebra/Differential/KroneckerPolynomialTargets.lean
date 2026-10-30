module

public import LogicLineages.ModelsAlgebra.Differential.KroneckerPolynomialDefinitions

@[expose] public section

/-! Exact actual-polynomial calibration suppliers for paper15's remaining
effective decision programme. Only a genuine coordinate box bounds aliases.
Nothing here claims arbitrary substitution is injective, and no decision,
quotient or computability correctness oracle is an input premise. -/
namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u

def kroneckerPolynomialMonomial : Prop :=
  ∀ (K : Type u) [CommRing K] (n B : ℕ) (d : Fin n →₀ ℕ) (a : K),
    KroneckerPolynomial.encode B (MvPolynomial.monomial d a) =
      Polynomial.C a * Polynomial.X ^ KroneckerIndex.index B d

def kroneckerPolynomialCoefficient : Prop :=
  ∀ (K : Type u) [CommRing K] (n B : ℕ), 2 ≤ B →
    ∀ (p : MvPolynomial (Fin n) K) (d : Fin n →₀ ℕ),
      KroneckerPolynomial.Box B p → KroneckerIndex.Bounded B d →
      (KroneckerPolynomial.encode B p).coeff (KroneckerIndex.index B d) = p.coeff d

def kroneckerPolynomialDegreeBound : Prop :=
  ∀ (K : Type u) [CommRing K] (n B : ℕ), 2 ≤ B →
    ∀ p : MvPolynomial (Fin n) K, KroneckerPolynomial.Box B p →
      (KroneckerPolynomial.encode B p).natDegree < B ^ n

def kroneckerPolynomialInjective : Prop :=
  ∀ (K : Type u) [CommRing K] (n B : ℕ), 2 ≤ B →
    ∀ p q : MvPolynomial (Fin n) K, KroneckerPolynomial.Box B p → KroneckerPolynomial.Box B q →
      KroneckerPolynomial.encode B p = KroneckerPolynomial.encode B q → p = q

def kroneckerDecodedBox : Prop :=
  ∀ (K : Type u) [CommRing K] (n B : ℕ), 2 ≤ B →
    ∀ q : Polynomial K, KroneckerPolynomial.Box B (KroneckerPolynomial.decode B n q)

def kroneckerPolynomialDecodeEncode : Prop :=
  ∀ (K : Type u) [CommRing K] (n B : ℕ), 2 ≤ B →
    ∀ p : MvPolynomial (Fin n) K, KroneckerPolynomial.Box B p →
      KroneckerPolynomial.decode B n (KroneckerPolynomial.encode B p) = p

def kroneckerPolynomialEncodeDecode : Prop :=
  ∀ (K : Type u) [CommRing K] (n B : ℕ), 2 ≤ B →
    ∀ q : Polynomial K, q.natDegree < B ^ n →
      KroneckerPolynomial.encode B (KroneckerPolynomial.decode B n q) = q

def kroneckerPolynomialBoxExists : Prop :=
  ∀ (K : Type u) [CommRing K] (n : ℕ) (p : MvPolynomial (Fin n) K),
    ∃ B : ℕ, 2 ≤ B ∧ KroneckerPolynomial.Box B p

def kroneckerPolynomialProductBox : Prop :=
  ∀ (K : Type u) [CommRing K] (n B : ℕ), 2 ≤ B →
    ∀ p h : MvPolynomial (Fin n) K,
      KroneckerPolynomial.Box B p → KroneckerPolynomial.Box B h →
      KroneckerPolynomial.Box (2 * B) (p * h)

def kroneckerPolynomialQuotientBox : Prop :=
  ∀ (K : Type u) [Field K] (n B : ℕ), 2 ≤ B →
    ∀ p q h : MvPolynomial (Fin n) K, p ≠ 0 → q = p * h →
      KroneckerPolynomial.Box B q → KroneckerPolynomial.Box B h

def kroneckerPolynomialLargerBaseVerification : Prop :=
  ∀ (K : Type u) [CommRing K] (n B : ℕ), 2 ≤ B →
    ∀ p h q : MvPolynomial (Fin n) K,
      KroneckerPolynomial.Box B p → KroneckerPolynomial.Box B h → KroneckerPolynomial.Box B q →
      (KroneckerPolynomial.encode (2 * B) p * KroneckerPolynomial.encode (2 * B) h =
        KroneckerPolynomial.encode (2 * B) q ↔ p * h = q)

end LogicLineages.ModelsAlgebra.Differential.Targets
