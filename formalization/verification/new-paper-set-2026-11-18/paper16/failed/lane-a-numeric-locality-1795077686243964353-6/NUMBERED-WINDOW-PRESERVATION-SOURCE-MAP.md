# Numbered window preservation: source-first supporting target

Scope: the numerical half of paper16's locality argument, not the complete
numbered `lem:window-locality`, a positive simulation, a quotient-encoding
theorem, or `lem:arithmetic-accessibility`. The source is
`16-persistent-marking-termination-ordering/sections/ordinals.tex`; exact
source bytes and imports are pinned by `NUMBERED-WINDOW-PRESERVATION-FROZEN.json`.

| Source passage | Literal correspondence / obligation |
| --- | --- |
| 12–31, auxiliary syntax and fixed window | Existing `NumberedWindowSyntax` distinguishes auxiliary application from the original binary head. `InWindow S K C τ` keeps actual ordinary lexical typing, the full node and binder type support, and admission of each actual head with its original result and base-argument declarations even for a retyped numbered head. `S` is the fixed signature; list `K` is the finite subtype-closed manuscript type set. Typed global free names and arbitrary lexical `C` represent the fixed carrier; no irrelevant type in an unused position of `C` restricts the endpoint or its actual support. |
| 32–58, displayed types and fixed-window raw rules | `RawTypedAdmissibility` reuses the unmodified `RawStep` constructor witness. It assumes only independent ordinary lexical typing for the result; the successor's support and head-window membership are the conclusion, not a premise. In particular the skeletal Stat constructor does not on its own ensure its chosen list is typed at the target declaration, so one cannot prove preservation for arbitrary untyped skeletal successors or assume the stronger `WindowStep`. The identical binder context, current output type, signature, and type set are held fixed. Raw auxiliary application closes only over its function. |
| 60–68, primitive mark decrease and replacement | The mark-decrease branches preserve types, actual head, base, ordered extras, and all initial lambda binders (only omega-to-finite introduces the empty extras list). Stat's retained and replaced members come from the genuine source occurrences using the exact `PrimitiveReplacement` permutations; inserted members are actual mark-decrease descendants, not arbitrary terms. For Copy, owner copies use the existing original source declaration and the actual target declaration's argument types. |
| 70–76, congruence modulo equivalent heads and permitted permutations | `NumberedWindowPrimary.Primary` is typed at `C,τ`; root head exchanges require existing `Spine.Equivalent`, typed base lists of both original declarations, actual `List.Perm`, and both original heads in the same fixed window. Ordinary exchange fixes the ordinary result type. Numbered exchange fixes its current output type, finite label, and identical extras. `OrderedPrimary` is componentwise congruence at identical positional types, separately for base and ordered extras. Congruence preserves binder/domain/codomain annotations; allowing auxiliary argument *equivalence* does not add an argument-side raw step. `PrimaryAdmissibility` proves a two-way transfer of the full window guards, not just formerly present types. No least-code representative or finite-class cardinality claim is made here. |
| 219–225, preservation at every intermediate | `TypedTrace` records each actual raw witness or primary equivalence in a single fixed typed carrier. No constructor requires `InWindow` or the stronger `WindowStep` at any vertex. For raw edges both ordinary endpoint typings are explicit; for equivalence its typed inductive witness is the edge. `AllTypedTraceIntermediates` asks for full window admission of every actual vertex from only initial admission and closedness of `K`. Zero-step traces retain the initial vertex, and the final vertex is included. |

Proof obligations after target-only pass: (1) support/head transport along
actual de Bruijn shift and substitution with reinserted arguments, using
type-correct binders and preserving the lambda arrow annotations; (2) typed
inversion and recursive argument closure; (3) actual Select argument
membership, arrow-prefix subtypes, owner-copy support, and left-associated
auxiliary application; (4) Copy/Stat with actual target guard, primitive
replacement occurrence origin and mark-decrease support; (5) both
directions of the componentwise/permutation proof; (6) induction on the
literal supplied trace. These describe proof obligations, not available
proofs. The other completed symbolic-locality and tuple packets are not used
to remove or replace any premise of the comparator.

The endpoint is a uniform preservation supplier for all such independently
typed traces, not a construction of a trace for each original judgment.
The final numerical simulation must build the actual typed trace and use
the three exact helpers; this packet alone does not establish the
manuscript's global locality by definition. No author proof was written
and no native preflight run for this comparator at source freeze.
