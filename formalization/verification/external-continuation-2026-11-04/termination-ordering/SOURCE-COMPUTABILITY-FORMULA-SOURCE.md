# General-language type-recursive computability formulas

Parent reviewed exact targets and correspondence 2026-11-04 11:22 UTC. Standard comparator/freeze required before proof. No export or publication.

Paper06 lines572–581 defines typed computability predicates by finite type recursion, base I and arrow quantification over computable arguments. The semantic Computable definition here uses the accepted actual encodedTyped carrier and decodedApplication operation. P is an arbitrary interpretation of the single unary predicate, not an assumed ID1 fixed point.

At ground type the clause is encodedTyped ground x and P x. At sigma→tau it is encodedTyped (sigma→tau) x and, for every u satisfying the sigma clause, existence of z with actual decodedApplication context (typeNumber sigma) (typeNumber tau) x u = some z and the tau clause at z. Existence of successful partial application is essential; a vacuous implication from success is not substituted. Failed application cannot satisfy an obligation for a computable argument. No default numeric result is used.

The first target supplies a genuine first-order formula in the existing arithmetic language extended by one unary predicate, for each actual finite Ty, and proves its standard-N realization agrees with the exact semantic recursion for all P, context codes, and input codes. It must reuse the accepted typed-carrier and application graph formulas and prove binder-aware substitution calibration. This is a family of finite formulas for fixed types, not a single satisfaction predicate over arbitrary type codes.

General language is essential: the domain clause at an arrow occurs in an implication antecedent. These formulas are NOT asserted to belong to the Positive grammar or to be monotone in P. The second target records the typedness conjunct retained in every clause.

No subtype-closure or successful-context premise is needed for all-code formula calibration; the actual encoded predicates retain their failure semantics. Relating this to confined actual typed terms uses earlier calibration with its explicit subtype-closure hypotheses, not a new assumption here. This component does not prove computability implies I/accessibility, closure under H/R, variable/lambda/numbered-constructor computability, all-terms termination, or internal ID1 derivability. The original transitivity obstruction remains unchanged.
