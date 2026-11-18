# Actual partial entry and residue source map

The source E(lambda,nu)(t),tau(lambda,nu)(t) is the norm and count of the
first actual nonfinite descent state in [nu,nu+omega). `FirstEntry` specifies
that literal state and excludes every earlier hit. `entryNormAt` is its actual
additive hereditary norm. Initial state remains lambda+(t-N(lambda)). There
is deliberately no invented value when a small input skips a positive target.

For nu zero or nonzero limit, being in [nu,nu+omega) is equivalent to having
limit part nu. The numerical search uses the faithful raw split code to test
this equality, and Nat.rfind to require the first event. The output is norm
and count, not a surrogate suffix-kernel count. `EntryEffectivity` demands
Partrec and an exact bidirectional membership theorem on all normal initial
and eligible target codes. Invalid raw codes have no source interpretation;
no all-input totality is asserted. On the affordable source tail, actual hit
existence plus this equivalence must establish definedness.

`EntryExistenceOrbit` requires the exact displayed max{2,N(lambda),N(nu)}
tail, an actual first-hit witness, and its f-iterate norm. Prove this without
supplying an affordability/termination/hit oracle: before reaching the
interval, the target is an admitted predecessor, hence cannot be skipped;
actual strict descent forces an entry. Terminal nu=0 is included.

`EntryResidues` is the full printed proposition with nu limit-or-zero below
nonzero limit lambda, exact max{N(lambda),N(nu)+3,m,B_f} tail, finite-omega
intervals with positive k and exact count k, and complementary long intervals
with signed count residue p(t)-ceil(N(nu)/2) and norm residue2ceil(N(nu)/2).
Ceiling is (N(nu)+1)/2; odd prefix norm is not dropped. Both source controls
and exact B values are explicit through SelectedWithThreshold. No residue
premises are used. Relative propagation/gap rules, block arithmetic and the
main theorem remain separate.

## Proof dependency plan

1. Code split/actual interval equivalence, trajectory until hit, least-search
   membership; generic per-function Computable f gives Partrec.
2. Actual affordable target preservation, well-founded first-entry existence,
   uniqueness and norm orbit. Use actual limit-part dynamics, not the old Phi
   entry or suffix kernels.
3. CNF decomposition nu=P+omega*j with P exponents>=2, source norm equality
   N(nu)=N(P)+2j; finite-tail exact count on true actual coefficients.
4. Long interval reaches limit-part P+omega^2 before entry. Prove explicit
   budget f(t)>=N(P)+max(3,2j) from stated source tail, derive exact funnel
   coefficient f(v)/2-ceil(N(P)/2), then exact count formula.
5. Apply already-proved arbitrary selected-control potential orbit to cancel
   the unknown funnel index. Derive norm residue from actual entry orbit and
   evenness, without a supplied residue theorem. Add table-family consequences
   separately after the full proposition, preserving the identity field's odd bit.
