# Full native computable substitution: frozen preflight packet

## Source correspondence and precise scope

Paper 06, `06-godel-t-termination-ordering/paper.tex`, lines 620–622 states
structural induction under computable substitution for every S-term, followed
by membership in I. The preceding lambda argument (590–595) and ranked
constructor/multiset argument (604–620) are now supplied by checked native
endpoints. This packet combines those endpoints in the original mutually
inductive NumberedRewriteSyntax.AuxTerm/AuxArguments. All six term and both
argument constructors remain present. Original SourceMarked head syntax,
typed variable contexts, finite head windows, representative codes, encodedR,
and the actual least-set Computable relation are reused without alteration.

## Six exact targets

1. ActualWindowComputableSubstitution is the fundamental lemma with a
   computable-image premise guarded by membership of the variable type in the
   fixed finite universe. This is the same finite-type guard already used in
   GoodSubstitution, not a whole-term conclusion or new closure supplier.
2. ActualFullComputableSubstitution preserves the original applicative
   theorem's unguarded computable-image premise, removes its fragment predicate,
   and adds precisely the finite rank-certificate premise required by the
   checked full constructor endpoints. It follows from the stronger first target.
3. ActualArgumentComputableSubstitution covers every member of the substituted
   original AuxArguments list, with the original GoodArguments universe guard.
4. ActualAllTermComputable removes all substitution/environment premises by the
   original variable theorem and the identity substitution.
5. ActualAllTermLeast gives actual leastSet membership at the SAME tuple.
6. ActualAllTermAccessible gives Acc for the SAME actual encodedR relation.

Each endpoint retains context decoding, subtype closure, actual scalar/relation
calibration, a rank : Fin n → Fin n with rankCertificateTest ctx.2 rank = true,
and actual finite-universe membership. There is no assertion for cyclic
uncertified precedence, non-window terms, or arbitrary uncalibrated predicates.

## Why the guarded environment is necessary

An arbitrary Gamma may contain types outside the finite universe that never
occur in the term. The existing variable theorem proves C only when the type is
in that universe. Requiring C for all Gamma variables blocks the identity
specialization without an unnecessary new Gamma-in-window assumption.
WindowComputableEnvironment requires exactly the types the structural induction
can inspect. The unguarded original contract is separately preserved as target 2.
No computability fact is assumed for unused or non-window types.

## Source-first proof route, not an accepted proof

Use the original mutual term/argument recursor. Variable, bottom, application,
and lambda cases use already checked suppliers. In the lambda case extend the
source environment by an arbitrary actual computable argument, retain the SAME
Delta/context/scalar, and use actualExtendedBetaIdentity. No fresh-target scalar,
weakened-image C, body C, or body accessibility premise is added. Ordinary and
numbered cases use exactly actualOrdinaryConstructorComputable and
actualNumberedConstructorComputable on the recursively substituted argument
members and the unchanged certified precedence. The argument nil/cons cases
supply literal member computability. Identity substitution and the checked C-to-I
and C-to-accessibility endpoints give targets 4–6.

## Scope and immutability

Native semantic computability/accessibility only. No internal ID1 derivation,
source-to-internal I/C transport, full-root build, remote CI, source-register
completion, or unconditional precedence theorem is claimed. Paper06 lem:id1 is
not completed by this native packet. Existing accepted/frozen mathematical
sources and manuscript bytes are immutable. The author ran no compiler or Git.
Coordinator must validate this preflight before proof authoring begins.
