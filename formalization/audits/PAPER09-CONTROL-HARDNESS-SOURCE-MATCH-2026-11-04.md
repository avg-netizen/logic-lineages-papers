# Source match for paper09 control hardness

The numbered source is `09-canonical-source-expressivity/hardness.tex`,
`thm:control-hardness`: for every fixed b, strict and weak universal canonical
comparison are Pi-zero-one complete on ground-output sources with ground free
names and binders, primes only 0/S and internal level at most one; Gamma_b's
parity is not eventually periodic.

The existing `SourceControlHardnessBundle` supplies three independently frozen
targets, rather than a new theorem with weaker premises:

| Source obligation | Existing exact endpoint |
|---|---|
| Fix an effective enumeration and primitive-recursive bounded actual-transition test before choosing b or an input index | `Targets.ExplicitEnumerationClock` |
| Both fixed-b comparison languages are co-RE complete; Gamma_b parity has no eventual period | `Targets.FixedControlHardness` |
| Comparisons denote the literal canonical assignment under the norm-controlled maximum-recursion collapse | `Targets.CanonicalObservation`, with `ParametricActualCollapse.Targets.ExactRecursion` |

## Enumeration and control

The source explicitly fixes a bounded simulation for an unspecified effective
enumeration of blank-input programs. The proof chooses the actual finite-table
TM0 enumeration. Its checked test uses t+1 observations for at most t actual
transitions; no equality to `Code.evaln` stages is needed. Surjectivity, primitive
recursiveness, actual transition-clock calibration and computational completeness
of blank halting have been proved. `gamma b` is literally the existing
`PerturbedControl.control b boundedH`, so the additive-one control and its fixed-b
order of parameters are preserved. This adoption fixes that explicit formal
instance; it asserts neither identity with every machine enumeration nor a
runtime-preserving translation between enumerations.

## Independent input language

`SourceGammaRestrictedReduction.RestrictedSyntax` decodes a genuine context of n
ground names and two actual typed ground sources. `SourceGroundBinderFragment`
recurses over the original syntax: variables, zero, successor, application and
ground lambdas are admitted; case/recursor constants are excluded. Both terms
also satisfy the original internal type-support bound one. Canonical ground
contexts merely enumerate the finitely many independent ground names.

The language is not defined as the image of the reduction. The strict/weak
typed adequacy targets and exact syntax-class target cover arbitrary admissible
typed inputs in the restricted class, not just generated machine queries.
Both membership predicates quantify over every positive natural raw valuation,
with all occurrences of a free name shared. At ground output, the original
strict/weak vector convention reduces to strict/weak scalar comparison.

Malformed queries are rejected. The older `OriginalInput.CodedGood` language
uses Phi, a different tuple/flag codec and a vacuous malformed-query convention.
The numbered theorem here neither asserts that old language nor requires
all-code equality with it. Requiring that equality would add an obligation
outside this fixed-Gamma restricted source statement.

## Canonical semantics and completeness

The canonical transport uses the unchanged
`AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy` on actual source
terms. A collapse satisfying the independent maximum Equation gives exactly
the same finite scalar observations as the proved generic-control source
semantics. The actual `collapseWith G` satisfies that Equation and is unique
below epsilon zero; no unproved semantic oracle is installed.

`CoREComplete P` expands to the RE complement and the universal computable
many-one reduction property for every co-RE predicate. Both strict and weak
independent languages have those properties at each fixed b. The same bundle
proves Gamma_b primitive recursive and parity non-eventually-periodic.
This covers the numbered statement's three clauses.

The all-code numeric evaluator is not being confused with source semantics:
its typed calibration and positive raw valuation coverage are separate proved
dependencies. Fixed-b computability suffices for the co-RE upper bound. Later
primitive-recursive evaluation uses an input-dependent finite iteration count;
no joint-b primitive recursion or input-independent bound is part of adoption.

## Adoption boundary

The audit finds a whole-statement source match. Register promotion additionally
requires the fresh focused `SourceControlHardnessBundleStatementChecks` gate
and its actual standard-axiom audit; the portable result is recorded separately
in `verification/source-adoption-audit-2026-11-04/CONTROL-HARDNESS-CHECK.json`.
The focused check passed on 4 November 2026: 488 local modules were compiled,
the three fixed declarations passed their transitive allowed-axiom audits,
and the original compiler pause policy was restored byte-for-byte. The source
register now adopts this one numbered theorem. The root selects its existing
exact gate; neither the whole AG aggregate nor either unreviewed draft was
added to the root.

No unrestricted source-language identity, fixed-Phi transfer, functional-input
hardness, final tree/code-length/runtime bound, whole-root build or CI result
is inferred. No source manuscript, accepted definition, comparator or proof is
changed by this source match.
