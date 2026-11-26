# Planned proof order for the frozen numbered whole-tuple endpoint

This is a dependency plan only. Source semantics remain the four reviewed,
pinned numerical-window modules; no later proof or compiler admission is
implied.

1. **Representation.** Establish exact paired symbolic/numeric typing,
   support and head admission, threshold lowering, paired get/len, and
   shift/substitution structure. Every numeric input stays in the same
   declared window without a new premise. These four public supporting
   contracts are already frozen and use no decision port restriction.
2. **Numerical binding.** Pay the five source-first binding equalities
   separately. Singleton retraction under cutoff is simpler than the
   historical general block lemma. After it, singleton followed by
   prior block is exact by index partition: below the singleton depth,
   at its new front, inside the older block, and beyond both removals.
   Literal opened-body beta then follows by cancellation on the old
   base/extras, append distribution and shift-by-zero. This carries
   original numbered heads, bottom and auxApp without new axioms.
3. **Domain and application shape.** Independently derive numeric
   annotation equality; recover domain and suffix types from the actual
   original typed call. Under the frozen `Closed K` premise, these
   suffixes lie in K from the function's root type. Use the actual
   auxiliary app constructor and actual typed, admissible argument
   list to construct `applications Q As`. Transport a path through
   its remaining auxiliary applications using only `auxFunction`,
   and recheck the complete typed context and original declarations
   at every step. The induction hypothesis does not ask for a wider
   auxiliary path or stronger assumption on the original call.
4. **Numbered functional append.** Induct on the actual typed suffix
   tuple. At each step start at one greater leading label, build the
   literal numeric abstraction in the same window, beta to the actual
   marked owner with one more ordered extra, and lift through the
   remaining applications. Continue at the decremented label.
   Associativity is only of literal list append and raw auxiliary
   application construction, never source `Spine.apply`.
5. **Protected original prefix.** Induct on input args while keeping the
   original term's case distinction and the actual accumulated symbolic
   and numerical blocks. In the Lambda branch the next original beta
   is accounted for by the singleton push-block identity. The zero
   suffix is simply the realizing numeric substitution, including
   variables. In the nonempty suffix free/bound branches, actual
   `Spine.applyAux = some r` is impossible, regardless of the shape
   of an earlier substitution image. At an ordinary functional head,
   select a sufficient finite label by the actual mark rule; at an
   original marked head use its existing available finite label. Apply
   the actual complete functional append path in either case.
6. **Exact cap and public endpoint.** The original finite-prefix
   traversal consumes no finite leading label of a retained head.
   A head then spends only the remaining suffix length on finite
   decrements, plus the one possible initial omega mark. This proves
   the explicit `n + original args.length + 1` threshold and exact
   same result from the actual `some r` equation. No statement about
   the minimum budget, unrelated raw paths, positive paths in zero
   cases, or arbitrary original derivation locality is included.

For original typing, use already checked `SpineCallTypingProof` and
`SpineSubstitutionProof` at arbitrary outside contexts, not observed-input
closures at `EmptyContext`. General symbolic support after actual
substitution may project the existing general `DecisionSourceSubstitutionProof`,
instantiating its name/head parameters with finite actual syntax inventories
rather than adding its source-specific restrictions to the public target.
Keep any numerical typed context lemmas explicitly for the new syntax.
