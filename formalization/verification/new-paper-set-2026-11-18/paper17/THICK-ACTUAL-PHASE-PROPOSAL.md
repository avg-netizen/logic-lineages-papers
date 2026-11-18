# Proposed actual retained-block phase predicate (pre-freeze discussion)

Use a fresh clock at an actual common top visit, NOT supplied top-hit witnesses.
Parameters: same selected f,B; actual limit-or-zero offsets mu,nu; ordinary prefix
P; exponent a>=2, all below epsilon0; omega^a divides P (P may be0); natural q>R+2.
Let rho=P+omega^a*q, E=log_omega(rho), c=s_mu(E), c'=s_nu(E), with c<c'.
Require R>=20, Nmu<=R, Nnu<=R, N(a)<=R. These are consequences of source R and
its explicit exponent-norm bound, not a replacement for proving dynamic costs.

Actual starting heads A=mu+rho and A'=nu+rho are limits. Start both actual
descents at countInitial A s and countInitial A' s, with common s above their
norms and max(100*(R+2)^4, initialLcm(R+1), B). This is a reset of the actual
common clock: any source phase-start states with common norm s and these limit
parts must be proved equal to these countInitial states. No control is changed.
Relative phase states are their actual descent iterates minus mu/nu.

The retained q>=3 units force all three top prefixes rho, rho1=P+omega^a*(q-1),
rho2=P+omega^a*(q-2) to have the SAME E; fixed shifts at these states are derived
from actual CNF, not a supplied profile-constancy oracle. This realizes the source
fixed-leading phase and permits P=0, rather than requiring an extra nonzero prefix.

Desired visit-or-diverge bridge:
- Derive first entries into absolute mu+rho1 and nu+rho1 from actual existence,
  prove affordability via coefficient-drop norm identities and q>=3.
- If those hit indices differ, derive an earlier actual relative-limit divergence
  while both processes are still above rho2 (take earliest differing state, with
  actual target affordability preventing skips). No shared-hit premise is allowed.
- If no earlier divergence, derive same actual first-hit index. Apply full moving
  EntryResidues from the common fresh input s to these long target intervals.
  One omega^a step is >=omega². All target+3/modulus/B thresholds are derived.
- Round-charge rigidity then c'=c+1 and c+Nrho1 odd. At the NEXT actual common
  budget use decrement; actual local formulas at rho1 yield unequal limit parts.
  Derive both next relative limits >=rho2 (indeed generated positive tail), so
  separation occurs before retained block has been processed.

Candidate full local conclusion: exists an actual common-clock i with unequal
relative limit parts and BOTH at least rho2. This is stronger than merely different
entry counts and directly witnesses separation within the retained block. A bounded
witness <=min(two derived top-entry counts)+1 can be added if fully proved.

Open scope questions for review BEFORE freeze:
1. Is this reset-top formulation source-complete for “process common block,” or
   must we separately derive the first top visit from an arbitrary lower suffix?
   Source says earlier lower-remainder divergence already suffices. A full wrapper
   may need a general current rho+lower-suffix and an entry-or-diverge bridge.
2. Keep all source R/M/tail conditions visible; do not strengthen R>=Nmu+Nnu+Na
   unless explicitly derived. Do not supply any first-hit count/visited top as input.
3. The local conclusion is not yet a frozen full lem:thick target. If arbitrary
   phase admission remains unpaid, label this top-launch statement supporting.
