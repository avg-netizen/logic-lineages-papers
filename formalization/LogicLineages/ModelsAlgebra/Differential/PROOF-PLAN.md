# Differential-constraint dependency plan

The mathematical targets are the two stated constraint criteria in paper 15,
not a predicate defined by those criteria. The following chain preserves the
source's arbitrary differential-extension and designated-root quantifiers.
No item is accepted merely because a candidate file exists.

1. **Rational differential-polynomial semantics.** Use
   `MvPolynomial ℕ ℚ`, with its constructed derivation sending variable n to
   variable n+1. Evaluate at the actual sequence a, Da, D²a, ... . Prove
   evaluation commutes with the derivations. `PolynomialEvaluation.lean`
   contains this candidate construction and induction.
2. **Algebraic constants.** Differentiate the actual minimal polynomial and
   use its characteristic-zero separability. `Targets.lean` fixes the exact
   rational-base statement independently of `Constants.lean`. No hypothesis
   asserting that algebraic elements are constants is supplied to the proof.
3. **Generated differential fields.** Construct the smallest subfield
   containing all jets, prove it is closed under D, and prove the restriction
   of D to it is a derivation. Closure under inverse must be proved using the
   actual field derivative rule. This supplies the source's Q⟨a⟩, rather than
   naming an assumed generated-field interface.
4. **First-order evaluation kernel.** For irreducible p(Y,Z), positive
   Z-degree, and nonconstant a, prove that evaluation at (a,Da) has kernel
   exactly the ideal (p). Required ingredients are transcendence of a,
   Gauss's lemma, irreducibility over Q(Y), and contraction back to Q[Y,Z].
   Derive nonvanishing of p_Z from the kernel and degree decrease.
5. **First-order field and isomorphism.** The differentiated equation gives
   D²a = -p_Y(a,Da)Da/p_Z(a,Da). Prove Q(a,Da) is D-closed. Construct the
   field isomorphism between two solutions through the common curve
   function field and prove it commutes with D on both generators and
   throughout the field. No designated-root isomorphism is assumed.
6. **Generic first-order witness.** In the fraction field of Q[Y,Z]/(p),
   construct the derivation with Dy=z and Dz=-p_Y z/p_Z. Show the relation
   ideal is stable under this derivation before descending/localizing it.
   Prove y is transcendental, z nonzero when p(Y,0) is nonzero, and every
   given nonzero q(Y) is avoided. This avoids a new existence oracle.
7. **First-order exceptional roots.** Formalize r=p(Y,0), its rational
   squarefree part, and the equivalence between divisibility into q and
   vanishing of q at every algebraic root of r. A missing irreducible
   factor supplies a constant counterexample; the generic witness supplies
   the nonconstant one. For r=0, irreducibility gives p associated to Z,
   and two distinct rational constants avoiding q refute constrainedness.
8. **Splitting-field derivation.** The pinned Mathlib already constructs
   finite differential-field extensions and proves uniqueness in
   `Mathlib.FieldTheory.Differential.Basic`. For a solution field, a finite
   splitting extension suffices to expose the rational characteristic
   polynomial's roots. This can avoid introducing an unproved derivation
   on an entire infinite algebraic closure. The roots are algebraic over Q,
   so step 2 makes them constants; prove the extended derivation is linear
   over their constant splitting field.
9. **Distinct-weight independence.** First prove the product/power rules
   for eigenfunctions of a concrete base derivation. Rational linear
   independence makes the monomial weight map injective by scalar
   restriction. Standard eigenvector independence then gives independence
   of all evaluated monomials, hence injectivity of actual multivariate
   polynomial evaluation. `SpectralTargets.lean` and
   `SpectralIndependence.lean` specify and propose this chain.
10. **Spectral coordinates and exact root fields.** Prove the interpolation
    identities defining each coordinate, Vandermonde invertibility, and
    R_f(a) as a nonzero constant times their product. Apply step 9; the
    recurrence f(D)a=0 then proves the first n jets generate Q⟨a⟩. Build
    the root-designated differential isomorphism over Q itself.
11. **Rational product and necessity.** Define the product over the
    splitting field and prove its rational descent, or define the rational
    resultant first and prove the product formula after coefficient
    extension. Prove divisibility descends to Q. If R_f does not divide q,
    a missing coordinate gives a solution avoiding q and annihilating R_f;
    compare it with an all-coordinate rational-function-field solution.
    Those derivations must be constructed and extended to fraction fields.
12. **Effective conclusions and cyclotomic family.** Prove a rational
    resultant/division algorithm and the squarefree-gcd algorithm terminate
    and decide the stated predicates. Classical decidability alone is not
    the paper's effectiveness claim. Prove prime cyclotomic independence
    from irreducibility and the zero constant coefficient, and show the
    recognized family has unbounded differential orders. The general
    independent-spectrum theorem remains a promise-input decision result.

The full first-order criterion requires steps 1–7 and its algorithm in
step 12. The full spectral criterion requires steps 1–3 and 8–12. They do
not become proved by taking the isomorphism, generic witness, constant-field
extension or arithmetic algorithm as an extra theorem hypothesis.

## Fraction-field extension supplier

The pinned `RingTheory/Derivation/` files do not provide a direct
fraction-field derivation constructor. A concrete route is to encode an
actual derivation `D : Derivation K R R` by the algebra homomorphism
`r ↦ (r, D r)` into the square-zero extension of a fraction field `F`.
The actual `TrivSqZeroExt.isUnit_iff_isUnit_fst` theorem makes every
localized denominator a unit in that target. `IsLocalization.lift` can
therefore extend this ring homomorphism to `F`. Localization extensionality
proves that its first projection is the identity. Its second projection
is the required derivation, by the proved addition and multiplication
projection laws. Scalar linearity follows from the image of base constants.

Relevant existing suppliers are
`Algebra/TrivSqZeroExt/Basic.lean` (projection, multiplication, and unit
criteria) and `RingTheory/Localization/Basic.lean` (localization lifts).
The encoding homomorphism, denominator-unit proof, projection identity,
linearity and restriction agreement still need actual project proofs;
none is currently an accepted theorem or an assumed interface.
