# Non-lambda application: raw step and one quotient edge

Draft requested 2026-11-04 13:40 UTC. Exact review/comparator/prospective freeze required before proof. Verification-only/no export.

Paper06 lines583–589 uses the reduction behavior of a non-lambda application. Target one gives exact iff raw WindowStep inversion under literal isLambda f=false: app f a steps either to whole-term bottom, or to app g a through one genuine function-side step f→g. The same argument a is unchanged. No raw confinement assumptions are required, and no application-argument step is introduced.

Target two treats exactly ONE actual QuotientEdge H, not arbitrary positive paths. It fixes finite n, symbols/S/above/Gamma and explicitly assumes SubtypeClosed S, InUniverse f/a and non-lambda f. An H successor code of the actual representative of app f a is either the exact bottom representative or the representative of app g a for a confined same-type g with a genuine H edge from rep f to rep g.

The actual H witness may start with a primary-equivalent application f' a', not literally f a. Accepted typed application component decomposition supplies genuine WindowPrimary on both components at the same types. Outer lambda invariance keeps f' non-lambda. Actual window/confinement preservation supplies the needed component/target confinement. Argument variation is discharged using actual application primary congruence and canonical representative equality, never by inventing an argument reduction. The target returns the original a exactly at the representative level.

No full-path endpoint classification is asserted. In a longer R path, a function can first become a lambda and then beta-reduce, so later endpoints need not remain an application. A future full-path lemma must preserve a first H successor plus equality-or-residual-R. No expansion/computability, ID1, all-term accessibility or original-order transitivity conclusion is included.
