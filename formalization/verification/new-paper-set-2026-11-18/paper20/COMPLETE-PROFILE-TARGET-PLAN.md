# Current paper 20: exact complete residue-profile target plan

Source: `20-controlled-descents-and-cartier-observers/sections/cartier.tex`, `lem:binary-transient` and `thm:residue-observer`. Investigation only; no new accepted target or native proof claimed.

## Reuse boundary

The old `FullActualBinaryHigherPoleRemoval` is a genuine statement about the literal mapped denominator A_d, every finite Laurent coordinate and literal ceiling-log transient. But its operator is `(actualDifferentialCartier)^[a]`: repeated L1 only. In particular the repeated-Cartier scalar formula uses the fact that a higher pole never becomes simple. That fact is FALSE for mixed words: an order-two pole under L0 becomes an order-one pole. Original simple residues therefore cannot supply the mixed observer's initial profile without computing the transient.

`ActualBinaryRationalCartierUpdate` likewise uses only `actualBinaryPolynomialDigit true`; its name does not supply the missing even transition. The existing rational square-root digit false is a genuine canonical fraction operation, but identifying it with C(X*f) and transporting it through the source denominator remains a proof obligation.

Useful existing, genuinely typed suppliers (subject to source-matched native closure checks at use):

- `CartierRationalDefinitions/Proof`: canonical RatFunc square decomposition and uniqueness; actual C is its odd square-root part.
- `CartierLocalProof`: actual integer-power local rule and square pullout.
- `CartierLaurentProof`: exact translated Laurent coefficient rule for C.
- `CartierProperProof`: actual canonical numerator-degree properness and C preservation.
- `BinaryPoleBudgetProof`, `BinaryPoleRemovalProof`: actual source initial denominator multiplicity/support budget, literal mu and ceiling-log a.
- `BinaryCartierExtensionProof`: genuine F2 rational extension/injectivity and commutation with C.
- `BinaryCartierUpdateProof`: complete rational-state equality for L1, not L0.

Search found no existing residue-profile compatibility space or partial-fraction profile bijection in the ordinal-comparison tree.

## Fixed mathematical definitions for the full target

Use actual `RatFunc K`, not an abstract state or a structure with transition laws assumed as fields. Fix d and a finite splitting field K of actual A_d over ZMod 2, characteristic two and perfect. Define S to be the FINITE SET OF ALL DISTINCT ROOTS of actual mapped A_d. Prove its nonzero and Frobenius-stability properties from A_d; these cannot be extra assumptions in the final source-specialized theorem.

Define P_d as the subtype of functions b : S -> K satisfying b(z^2)=b(z)^2. Define PF(b) = sum over ALL z in S of C(b(z))/(X-C(z)). Define L1(f)=actualDifferentialCartier f and L0(f)=actualDifferentialCartier (X*f). Define T1(b)(z)=sqrt(b(z)), T0(b)(z)=sqrt(z*b(z)), and output(b)=sum b(z)/z. Define binary execution by a left fold, explicitly tying list order to the low-bit-first selector convention. No coordinate omissions or quotient by scalar outputs.

Define source rational states independently of PF as proper F2 rational functions whose extension to K has only simple poles among S, e.g. denominator divides the actual squarefree part S_d, with a proven equivalence to the Laurent simple-pole condition. Defining the state space to be `range PF` would make surjectivity vacuous and is not acceptable.

## Full theorem obligations (conjunction, not interchangeable partial substitutes)

1. P_d finite and PF gives an equivalence with the independently defined F2 simple-pole rational states. Pay uniqueness/injectivity, partial-fraction existence, coefficient Frobenius invariance iff compatibility, and descent to F2. Include zero and d=0/empty roots rather than silently restricting them.
2. Both T0 and T1 preserve compatibility. Prove their actual F2 linearity if retaining the source proof's stronger assertion.
3. Actual RatFunc identities L_i(PF(b))=PF(T_i(b)) for i=0,1. In particular prove C is additive for the finite sum; pullout alone is not additivity. The L0 local computation must kill its constant term.
4. Actual evaluation at zero of PF(b) is output(b), and output is Frobenius-fixed / belongs to embedded F2. Nonzero roots justify evaluation; prove descent, not just equality in K.
5. For every remaining binary list w, actual selectors applied to PF(b) equal PF(fold T w b), and the resulting constant coefficient equals output of that final profile. Prove the bridge to actual F2 binary selectors, not merely define selectors to mean profile updates.
6. For every proper input U/A_d and EVERY word w of length a=Nat.clog 2 mu, actual mixed execution stays proper, has no new pole and only simple poles. Its exact resulting profile is obtained from that resulting rational state, not the initial simple residues. Combine this with 1–5 to prove the source's final post-transient observer claim.

The following prose paragraph's exact cardinality `2^(degree squarefree A_d)` is valuable but not a separate numbered theorem; if omitted from the first target, explicitly record that scope. Effective factorization/construction is also not supplied by a bare noncomputable splitting-field instance.

## Recommended implementation order and exact first scoped target

The full theorem is not a short comparator over existing results. First freeze a supporting mixed-selector supplier, not a promotion of `thm:residue-observer`:

For every perfect characteristic-two field K and f : RatFunc K,

`actualDifferentialCartier (RatFunc.X * f) = actualRationalSquareRootDigit false f`.

For every z,b in K and integer k, prove the actual L0 local rule:

- k=2j, j>=1: L0(b/(X-z)^(2j)) = sqrt(b)/(X-z)^j;
- k=2j+1, j>=0: L0(b/(X-z)^(2j+1)) = sqrt(z*b)/(X-z)^(j+1).

Use literal RatFunc expressions and inherited sqrt; no supplied local-rule hypothesis. Then derive the mixed Laurent support contraction (the L0 coefficient at n depends on original coefficients 2n and 2n+1), mixed properness and arbitrary-word source transient. In parallel the profile/descent/bijection layer is a substantial separate proof lane. Only after all these obligations have exact checked suppliers should the full conjunction and frozen statement comparator be compiled/promoted.

No compiler run performed for this plan. Parent review should choose the first supporting packet; no old theorem is relabeled as the full new theorem.
