# Literal auxiliary coding and primary-class bounds

These are prerequisites for the source finite/computable primary-class claim,
not that claim itself. Codes retain the actual constructor, de Bruijn variable
index in a fixed ambient context, binder/application types, literal head and
all native annotations, numbered label and output, full ordered base and
extra tuples and their actual type lists. Structural and packed injectivity
are unconditional; executable equality assumes only DecidableEq Symbol.
There is no numeric-code or new quotient representation claim here.

The executable maxLabel bounds every actual finite label. Ordinary heads
remain a separate constructor (implicit omega), not a finite label. Actual
primary equivalence preserves every label-bound predicate; together with the
previously proved size invariant this bounds each restricted class by its
source size and maximum label. The size equality is explicitly reused, not
counted as a novel invariant. No bound is inserted into primary generators.

Exhaustive finite typed/code enumeration, primary decision, least-code class
representatives and induced arithmetic reduction remain to be derived.
