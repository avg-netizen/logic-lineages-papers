# Specialize the actual joint program by its supplied policy index

Paper 17's main theorem says “uniformly in a supplied computable admissible
literal parsing policy.” This generic, conditional last mile produces the
index transformer from a *single* joint partial-recursive natural program.
It neither chooses a decider separately for each policy nor asserts such
a joint program has already been constructed.

A joint program takes the pair of the encoded Mathlib `Code` for the
literal selector and the encoded comparison payload. The pinned library's
`Code.exists_code` supplies one code, then `Code.primrec₂_curry` and
`Code.eval_curry` give the primitive-recursive specializer and its exact
partial evaluation. The same code works for all policy indices; when
the joint program has a successful Boolean-answer contract on admitted
inputs, exact specialization preserves that contract without being total
on arbitrary indices or silently defaulting divergence.

The existing fixed-policy comparator and evidence are untouched. The
actual joint indexed assignment, subsequent ground driver, and inhabited
admissibility/answer contract are separate proof obligations.
