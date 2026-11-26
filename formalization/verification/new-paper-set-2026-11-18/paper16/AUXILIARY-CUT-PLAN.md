# Actual auxiliary refinement and ordinary-final cut

Authoritative source: composition.tex, all seven additional weak rules,
syntactic refinement (S), lem:sharp-syntax, lem:prefix-escape, conservative
elimination, compression/admissibility/marking/two-environments/application
covariance/target macros, and thm:cut. Existing literal W/S and all original
spine/mark/typing definitions stay unchanged. Never replace full application by
iterated unary application. The checked blocking counterexample remains valid.

## Finite syntax, not an oracle

Represent auxiliary derivations and refinement witnesses as finite inductive
*data trees*, with logical relations defined by existence (Nonempty) of the
corresponding tree. This exposes actual recursive constructor-count functions
without illegally eliminating a Prop derivation into Nat. All comparison,
strict, matching, ordered-extra matching, replacement, supplier and Whole trees
are counted. Proof premises for typing/validity/freshness do not supply any
comparison theorem. Original W is still the existing Prop relation; embedding
into auxiliary tree existence is proved by its actual induction, not inserted
as an arbitrary embedding constructor. A data tree is neither coinductive nor
an assumed rank/derivation supplier.

## Refinement relation

Variables refine only the identical typed variable. Lambdas use the reviewed
same-fresh-opening presentation. Ordinary heads retain the exact symbol and
positionwise refining bases, not a head-equivalence/permutation shortcut.
Marked roots retain exact symbol and output annotation, positionwise refining
base lists, and a finite target-extra witness list. Each target occurrence d
has either (i) an actual source-extra At occurrence e, same outer type, with a
smaller refinement tree e -> d; or (ii) a smaller tree from the whole source
owner retyped to d's type into d. No order or multiplicity matching is imposed
on extras; witnesses may reuse a source extra. Whole-owner recursion is a real
strict subtree in the mutually inductive definition. All endpoints remain
actual typed/signature-valid auxiliary terms in the empty outer bound context.

## Literal prefix and extra witnesses

Define Prefix prefix extras by literal list prefix (same terms in same order).
A prefix copy changes only output type and truncates the owner's extra suffix;
head/base stay exact. Prefix tuples have the selected argument's arbitrary
finite arrow-prefix domain list, including zero arguments and functional final
type. Define permutations by one-occurrence removal, carrying typed terms
unchanged; no deduplication. Prefix-copy lists may repeat copies arbitrarily.

## Extended comparison

Copy the exact original eight weak constructors and Strict, replacing every
recursive premise by the auxiliary relation. Add exactly:
In: head equivalence, weak base occurrence matching, ordered extra matching.
Marked1/Marked2: strict head precedence / equivalence+base replacement, and
whole-source premises to every target base and extra.
Drop: append any well-typed/signature-valid source extra list.
Perm: permute source extras with the actual positional permutation witness.
Copies: remove an appended finite list of literal prefix copies of the
unexpanded source owner from a successful premise.
PSelect: selected term remains an actual base/extra occurrence; actual full
call succeeds on a typed tuple of literal prefix copies.
No auxiliary target-ordinariness rule is imposed. Marked reflexivity and marked
strict self-comparison are expected, not evidence of a well-founded relation.

## Dependency order, with no circular cut assumption

1. Refinement syntax reflexivity/transitivity, two-environment substitution,
   opening/renaming, root retyping, successful marking reflection, and successful
   actual full-call covariance. Structural transitivity precedes call covariance.
2. Literal omission/permutation/prefix-copy instances and two-stage prefix escape:
   staged success implies either the combined full call has that result, OR the
   retyped owner refines the staged result. Never assert unconditional full-call
   associativity. The original-variable branch is the second disjunct.
3. Original embedding, auxiliary reflexivity, and ordinary-target elimination
   by actual auxiliary derivation induction with arbitrary refinement witness.
4. Extra compression using only In/Drop/Perm/Copies; refinement admissibility
   using compression, not comparison cut.
5. Marking transport and two-environment substitution. Then application covariance
   uses prefix escape + refinement admissibility, not cut. Only already-successful
   full calls may be identified with their unary sequence.
6. Target-extra macros by derivation induction, no transitivity premise.
7. Cut on lexicographic (right tree size,left tree size), where every weak/strict/
   multiset/supplier/Whole/ordered-matching subtree contributes to size. Transport
   actual occurrence partitions and allow discarded sources without insertions.
   Use ordinary-final elimination after constructing the auxiliary comparison.

Initial reviewed freezes should cover concrete syntax and a small exact first
refinement/embedding packet. Full thm:cut target remains the actual conclusion
W s u from auxiliary s->t and t->u and Ordinary u; no composition oracle,
cut hypothesis, weak transitivity premise or all-ordinary intermediate condition
may be added. Larger claims wait for their real dependencies and evidence.
