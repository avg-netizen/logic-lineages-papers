# Native acceptance notice

The source-match review below was completed before the native verification. Its original pending-native wording is retained as historical review context. See [component acceptance](ACCEPTANCE.json) and the [passed native verification](../finite-source-comparison/NATIVE-VERIFICATION.json) for the subsequent result.

---

# Original ground admissibility and vector comparison

## Source contract

This component supplies the domain identification used in paper 08,
`thm:finite-source`, `paper.tex` lines 202–234, especially the positive-coordinate
tests at lines 213–216 and the admissible-ground-substitution argument at
lines 222–225. It is a supporting result; it does not itself prove the
finite-coefficient test, a decision procedure, or the numbered theorem.

The original WW domains are the existing `Source.OriginalDomain.ClosedGrade`
and `AdmissibleSubstitution` in `WWOriginalDomainDefinitions.lean`, corresponding
to WW Definitions 2.5–2.9. A substitution assigns an actual closed graded
expression to every component of a typed variable vector and satisfies the
original bounded-norm requirement. No new positivity, finiteness, semantic
equivalence, or decision field is added to that structure.

## Exact domain bridge

Every name in the free context has ground type, so each original variable
vector has exactly one component. The established `originalClosedScalarFinite`
and `originalClosedGradePositive` theorems show that each substituted component
has a positive finite ordinal value. These are proved facts about the original
closed domain, not assumptions about the substitution.

Conversely, each positive natural valuation is realized by the literal closed
Add/One numeral in `UnitObservation.substitution`. Its grade is proved by
construction; its boundedness is reflexivity for the single ground component.
Every original variable identity is retained and receives its own specified
value. Neither the input names nor their occurrences are duplicated.

`ExactGroundValuations` establishes equality of the entire ordinal-valued
valuation functions in both directions. Its use of classical choice is only
in a propositional extraction witness; this component makes no computability
claim about that witness. The executable source comparison pipeline remains
the independently accepted pipeline on natural codes.

The comparison relation uses `OriginalDomain.expressionValue` on each literal
`ordinalVectorAt` expression. Thus the original Zero padding is preserved.
Mode 0 is weak in every coordinate; mode 1 is strict only at coordinate zero
and weak at every positive coordinate; every other mode is equality at every
coordinate. The positive coordinates may be arbitrary ordinal expressions in
the generic bridge. Their actual-source closure and closed evaluation are
separate accepted results, not premises needed for domain equivalence.

The original support-restricted substitution convention is independently
covered by `WWOriginalSupportProof.originalSupportComparisonBridge`: unsupported
names extend by One, and restriction preserves the expressions on their exact
support. The present component works with the established total-context
`AdmissibleSubstitution` interface and introduces no additional restriction on
the occurring ground names.

## Canonical sources and boundaries

`ActualCanonicalComparison` obtains both canonical assignments from
`actualAdmissibleAssignmentGenerated` using the original terms and the fixed
`OrdinalSyntax.defaultPolicy`. It requires the same original result type and
ground free context. It neither normalizes the terms nor assumes assignment
or scalar-compiler success. Recursors and arbitrary internal types are allowed.

The coefficient finiteness predicate, literal collapse traversal, finite-source
recognition and comparison decision are outside this component. The bridge is
independent of those restrictions and does not discharge unrestricted BASE,
general Phi alternation, or any numbered-source obligation by itself.

## Freeze and verification

The independent definitions and four exact targets were written and SHA-256
frozen in `FROZEN-TARGETS.json` before the proof file was authored. No existing
source, target, gate, checker, dependency, or resource setting was modified.
The statement-check file aliases the four frozen propositions and requests an
actual namespace axiom audit. The author did not run Lean. Native acceptance,
source-bound receipts and final adoption are owned by the coordinator.
