# Actual comparison target ordinariness

Both frozen WeakTargetsOrdinary and StrictTargetsOrdinary compile under the
original fixed core profile, final receipt `1794980413238707262-2`.
Read-only verifier reconciles 12 modules, two aliases, zero errors, and only
standard propext/Quot.sound axioms. Frozen relation/targets unchanged.

Proof uses the actual generated six-way mutual derivation recursor, with
ordinariness motives for Weak, Matching and Whole. Unused Strict/Multiset/
Coverage motives in this Weak proof are True, not assumed ordering laws.
Matching reconstructs occurrence-list ordinariness after a single removal;
Whole supplies every target base. Actual substitution reflection recovers
ordinary original bodies from ordinary freshly opened bodies. The Strict
endpoint inherits the Weak target from its actual constructor.

Initial failed proof and receipt `1794980364324814917-2` retained. Repairs:
pass the source ordinary premise to removal induction; explicitly identify
opened bodies; replace unsupported partial mutual structural recursion by
actual full recursor use. Native diagnostic receipt `1794980388536196699-2`
printed that recursor; source retained under diagnostics, not production.

This proves the target-ordinariness constituent of elementary laws on the
reviewed auxiliary carrier, not strict inclusion or ordinary reflexivity.
Full alpha characterization/comparison derivation transport and complete
numbered lemma remain pending. No full-root build or CI claim.
