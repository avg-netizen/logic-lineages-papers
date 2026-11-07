# Uniform internal source application

This target assembles the application case needed by paper 06, `lem:id1`, in
the original context-uniform presentation. One source checker package, one
computability checker package, and one result-builder program are selected
before all source windows, precedence tables, ambient contexts, simple types,
and symbolic arithmetic terms.

The proof extends the same `GammaGuardedSource` witnesses used by the previous
application package. Its source relation and inductive body are unchanged.
The modified application checker is the existing
`InternalApplication.computability` construction, with its already proved
calibration to the original application semantics on every input.

The new rules assert computability of an accepted original application result
and of the output of the original result builder, from the literal function
and argument computability formulas and their original same-context guard.
The generic rules' window and arrow-code metadata are discharged by internal
numeral-evaluation derivations for the fixed context and simple types. They
are not added as premises of the source target.

The same selected witnesses retain the prior internal typed-successor rule,
ground computability downward rule, application totality and uniqueness, and
same-context guard transport. Retaining these clauses explicitly prevents
combining facts about unrelated existential presentations.

This proves the application consumer. It does not assert the lambda case,
constructor computability, arbitrary-type reduction closure, or the all-term
internal derivation. The numbered `lem:id1` endpoint remains pending.
