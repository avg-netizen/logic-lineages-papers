# S4 proposed paper08 kernel convention and signed-domain repair

Status: proposed for root review; no manuscript or source register changed.
Baseline: ba9237a98a20e24a87c2c95e91df67a185c11511.

This is an explicit mathematical correction, not a claim that the old printed
process equals the companion process. Existing accepted definitions, proofs,
targets and negative evidence remain unchanged.

## Proposed source changes

1. Paper08, Exact finite-degree prefix kernels, currently starts at omega^d
   and replaces the whole nonfinite suffix by its greatest smaller suffix at
   budget f^i(t)-c. Replace the transition by: at suffix eta+n, where eta is
   its nonzero limit part and n is finite, replace it by M(eta,f^i(t)-c).
   Keep the initial state omega^d, original time-indexed schedule, first-finite
   stopping rule and count of one replacement per step. Require d>=1 and
   t>=c+d+1. This explicitly adopts paper07 def:kernel's limit-part rule.

   Before: M(eta+n,b). After: M(eta,b). At omega+1 they can differ: the
   former can return omega and the latter is finite. The proved strict
   quadratic count discrepancy for every t>=4 at c=1 remains evidence
   against the old interpretation. No larger cutoff repairs it.

2. After defining signed X, specify admissible signed pairs as d>=2 with
   arbitrary j in Z, or d=1 with j>=0. Continue to require positive depth
   E^d_c(t)+j. For d=1, E=1 and positivity is equivalent to j>=0; there
   is no positive-depth tail for negative j. For d>=2 the existing explicit
   lower-bound theorem supplies a positive-depth tail for every fixed j.
   No inverse function or zero-clamped extension is introduced.

3. In lem:kernel-recursion, keep the unsigned count and unshifted value
   recurrence for every d>=2. State the signed value recurrence only when
   d>=3 or j>=0. At d=2, negative offsets are evaluated by the existing
   exact formula X^2_{c,j}=V_{j-ceil(c/2)} on their genuine positive tail.
   The degree-one child in the old d=2, j<0 clause is undefined; the
   checked j=-2 strict counterexample forbids silently clamping it.

4. In lem:kernel-residues, quantify d>=1, c>=0, m>=1 and admissible
   (d,j) as above. Keep the displayed residue formula and effective-tail
   assertion unchanged on this domain. The counter clause itself needs
   no signed restriction and remains valid for all d>=1.

5. Lem:counter requires only the convention change, with all ranks r,s>=3,
   original expansion/collision/order clauses and arbitrary retained
   masses preserved. Make the pair-dependent common sufficient tail explicit
   in the correspondence. Reuse the complete CounterSourceTheorem rather
   than rebuilding its constituents.

## Exact bridge to be checked

Independently define the proposed source budget B(i)=f^[i+1](t)-c and its
first-finite limit-part scheduled count directly at omega^d. Prove that this
count equals actualSuffixKernelCount omega^d c t on t>=c+d+1, and that the
source scheduled states agree with the companion's padded states from the
first replacement through the finite exit. Padding is
omega^d+(t-c-N(omega^d)); it records the initial total norm without adding
a counted replacement. The first replacement is M(omega^d,f(t)-c) in both
processes. Subsequent budgets agree because the existing trace proves total
norm f^[i](t) through the exit. The original schedule is retained throughout.

This bridge is stronger than merely renaming the existing kernels and does
not assume the desired equality. It will use actualKernelStartup,
actualSuffixKernelTrace, actualFiniteKernelSchedule and scheduled
first-finite uniqueness. Source-shaped exact targets and a comparator will
be frozen and preflight-compiled before proof authorship.

## Dependent effects and limits

- All existing counter clauses, leader chains, collision residual ranks,
  true integer differences, fixed-shift results and uniform tail maps stay
  mathematically intact under the selected corrected process.
- The downstream displayed finite word alphabet uses X of rank>=3 and V_j;
  these remain admissible. Their existing missing uniform-separation,
  cancellation, guard and arithmetic-decision proofs are not supplied by
  this repair and receive no automatic promotion.
- The genuine prefix splitting formula now uses the same limit-part
  transition as the imported paper05/07 controlled collapse evaluator.
- Old targets and all signed/whole-state diagnostics remain immutable.
  Any numbered completion must refer to the corrected source revision and
  an independently reviewed exact gate. No old printed statement is proved
  by interpreting its undefined terms differently.

Requested root review: approve or revise the five concrete source changes
before any manuscript edit or numbered source-register promotion. S4 may
develop the explicitly proposed bridge as an isolated component meanwhile.
