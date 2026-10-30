# Completed relative-cut chain

This plan is now historical: corrected/refrozen basic gates passed at
1793319466131889479-2; general conjugacy and both complete source07prefix and
10fixed source gates passed FIRST TRY at1793319734291867812-2. The original
new-definition parse bug was never accepted. Current acceptance is pinned in
ACCEPTED-RESUMED.json and PREFIXTRACE-FREEZE.json revision2. No repair described
below remains outstanding.

# Relative cut continuation

Current source objectives are paper07 `lem:prefix` and paper10 `lem:fixed`.
The source actual CNF min-exponent/divisibility, ordinary norm concatenation,
full compatible-prefix maximum identity, exact numerical fixed-budget count,
and actual partition-state cardinalities already pass. See ACCEPTED-RESUMED.

The new unaccepted PrefixTrace comparator had one parse bug. Corrected
`PrefixTraceDefinitions.lean` now explicitly uses
`((actualControlledStep g)^[k]) a`. Preserve the superseded freeze; compile
corrected definitions/targets, refresh PREFIXTRACE-FREEZE with the old record
identified as superseded, then repair/compile PrefixTraceBasicProof. Remaining
actual diagnostic in that proof is `Ordinal.mul_add`, which should be the
ordinary global `mul_add`. Other zero/successor type mismatches came from the
wrong iterate and should disappear after correction. The source target file
itself need not be weakened or changed.

Next prove ActualPrefixControlStep using:

* e>0 plus actualMinExponentDivisibility gives omega divides prefix.
* ActualLimitPartPrefixAddition gives limitPart(k+r)=k+limitPart(r).
* ActualDivisiblePrefixNormAddition gives N(k+r)=N(k)+N(r).
* ActualDivisiblePrefixMaximum at limitPart(r) and the affordable total budget
  gives exactly the residual controller `prefixRemainderControl h (N k)`.

Then prove ActualPrefixControlTrace by induction on i<=C, where C is the
literal residual controller count. ActualControlledTraceFirstFinite supplies
all remainder bounds, nonfiniteness for i<C, and a finite final remainder.
Use the already proved last-step iterate equation to rewrite the successor
case and ActualPrefixControlStep. Each remainder stays <= initial r, hence
below omega^(e+1). This establishes every trace equality through the relative
cut, terminal finite remainder, and all prior total states >=k+omega.

For actual source compatibility, choose e as the head exponent of the normal
representation of the nonzero limit suffix. The first CNF pair gives
actualMinExponentAtLeast k e; normal CNF gives suffix<omega^(e+1). Infinite
suffix implies e>0 (e=0 would bound it below omega). Specialize h=Phi;
Phi(c+n)>c+n ensures prefix affordability for every remainder norm. The
residual controller is definitionally compensatedPrefixControl. Positive
count follows from the nonfinite count equation. This proves the full07
conjunction, without assuming that global terminal count equals relative cut.

For10, specialize h to the constant S, e to natural d>=1, remainder to
omega^d+n. finiteOmegaPowerBelowEpsilonZero plus finite-tail closure supplies
the domain; isSuccLimit_opow_left supplies infinitude; the normal CNF block
bound supplies remainder<omega^(d+1). Prefix affordability follows S>=N(k).
The residual controller is constant S-N(k). Rewrite its actual count using
actualNumericalFixedBudgetPartitionCount, yielding exactly p_d(S-N(k)).
This proves every retained-prefix trace, finite-cut endpoint, and prior lower
bound in the original full source fixed-budget statement. Only after both
full exact gates pass should numbered increments rise from ten to twelve.
