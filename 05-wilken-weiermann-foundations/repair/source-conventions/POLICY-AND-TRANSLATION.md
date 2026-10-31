# A finite binary policy, its source correspondence, and uniform translation

## 1. What is and is not fixed by the primary source

Definition 2.1 gives literal ordinal syntax, whose three binary constructors
are `Add(f,g)`, `ExpProd(f,g)` and `Psi(f,g)`. They mean natural sum,
`2^f ⊗ g`, and `ψ(ω ⊗ f ⊕ g)`, respectively. In particular the last two
constructors have immediate subterms f and g. Leaves are indexed variables,
0, 1 and ω. Definition 2.4 interprets closed trees as ordinals. Equality of
interpretations is not identity of trees.

Definitions 2.6 and 2.9 use a smaller graded syntax: actual coordinate
expressions have no zero leaf. Definition 2.18 first tests whether the
*whole* input is free of the tracked name. Its size and partial operators
therefore see the literal tree. On the other hand the source writes
finite sums, natural-number multiples, and vector operations without
choosing their full binary expansion. Its convention for left-associated
lambda-term applications concerns a different grammar. No association rule
for all these ordinal macros is stated in the inspected definitions.

There is consequently a family of literal readings, not a uniquely
specified AST-valued original assignment. `GENERATED-WITNESS.md` proves
that even their interpreted zero-history assignments need not agree.

## 2. Admissible macro-expansion policies

A policy ρ is a computable total rule choosing an ordered full binary tree on r ordered operand slots
at each of the finite-sum sites below. For r=1 it is the identity; for
r=2 it is the unique binary addition. Every operand slot is used exactly
once and is inserted as an unchanged subtree. The choice depends on the
macro site and arity, not the names, values, internal trees, or free-variable
status of the operands. A natural-number repeat of a subtree consists of
k separate copies in the same sense. No existing subtree is flattened,
reassociated, sorted, combined, evaluated or replaced by a normal form.

The sites and their precise scopes are:

* a finite numeral k>0 is a k-fold repeat of One;
* a numerical multiple k·u, k>0, is a k-fold repeat of the *whole* u;
* the active-sum partial uses a three-operand sum of the two partial
  coordinate trees and One;
* the active exponential partial uses the three operands
  `Repeat2(P_{i+1} f)`, `P_i g`, One. The Repeat2 operand remains nested;
* each positive abstraction coordinate sums the m+1 partial coordinates;
* abstraction coordinate zero repeats `(P_0 h_0)_0` exactly S_X(h) times;
* the ground box tail has the ordered operands f_0,g_0 and, when n>0,
  the *whole numeral* n. The policy includes its chosen three-operand
  association. Paper05's already stated choice f_0+(g_0+n) is permitted;
* all other additions displayed as two-operand clauses are binary nodes.

The integer S_X(h)=2^n Σ_i s_X(h_i) is computed in metamathematical
natural-number arithmetic from the already fixed literal input trees.
It is not an ordinal expression to be reparsed. An operand such as a
numeral or Repeat2 is not flattened into the surrounding sum's operands.
The primitive ExpProd and Psi constructors are never expanded into an
untyped general-product grammar.

### Padding is a role, not an expression rewrite

A vector records its *actual* level. A lookup beyond it returns a special
absent value. For comparison this absent value is interpreted as zero.
In vector addition an absent operand is omitted; a present operand is
copied unchanged. If both are present an Add node is constructed. Every
actual output coordinate has at least one present operand.

The box's n=0 optional finite-level contribution is absent. This differs
from constructing a literal zero and then simplifying `+0`. For n>0 the
finite numeral n is present. Every sum in the partial and abstraction
clauses is nonempty. Their repeats have positive multiplicity. The source
prime 2 is the two-fold numeral, and prime 0 is assigned One, not Zero.

Thus every actual original-source coordinate is zero-free. A user-supplied
literal Zero subtree in the larger O grammar is not erased by this policy;
the smaller C/B domains simply do not contain it. Nothing authorizes
value-based zero elimination or normalization of a whole-free block.

This is an explicit elaboration convention needed to make the zero-free
graded clauses and the out-of-range-zero shorthand compatible. It is not
asserted to be a uniquely identified historical implementation choice.
The source itself supports this interpretation: footnote5 to Definition2.10,
printed page19, expressly says the asymmetric box definition facilitates
the C-syntax by avoiding occurrences of 0 in coordinate parse trees.
That explains the zero-free requirement; it still does not associate the
unparenthesized finite sums in Definition2.18.

## 3. Finite construction and exact source correspondence

Fix ρ once for the whole assignment. Expand the source definitions using
the preceding table, preserve each already constructed subtree, and run
the whole-free test before the active partial cases. Lambda-term source
syntax is never beta-normalized. The assignment derivation with empty
history at each lambda is now a uniquely determined ρ-canonical assignment.

The claim of uniqueness is *relative to ρ*. Erasing binary parentheses
introduced at a macro and restoring out-of-range comparison zeros gives
exactly the printed formulas of Definitions 2.10, 2.18 and 3.1. Repeats
have the printed multiplicity. Each interpreted sum or multiple has the
printed ordinal value for its given operands. Conversely every ordered
binary reading of these macro operands with role-based padding is one
of the policies just specified. No assertion of a unique original ρ or
cross-policy equality is hidden in this correspondence.

For a fixed input vector h, changing *only the output expansions* of its
partial or abstraction sums does not change their ordinal values: induction
on the fixed h uses associativity of natural sum and finite repetition.
This fact does not compare whole source assignments, since an enclosing
lambda applies its size and whole-free tests to the new output tree.

All operations terminate as finite AST constructions. Here is an explicit
bound rather than an appeal to unspecified finite notation. Let |u| be
the number of nodes of a literal ordinal tree, and define its weighted
tree size w by leaf weight one, weights w(f)+w(g)+1 for Add/Psi, and
2w(f)+w(g)+1 for ExpProd. Structural induction gives

    s_X(u) ≤ w(u) ≤ 2^{|u|}-1.

For any coordinate of P_i u, an elementary induction on u gives

    |(P_i u)_j| ≤ E(|u|),   E(t)=6·3^t.

Indeed a whole-free diagonal output has |u|+2 nodes; off-diagonal outputs
and tracked variables have one. Active sums have at most E(f)+E(g)+3
nodes; active exponentials at most 2E(f)+E(g)+4; a scalar collapse output
has at most |f|+E(g)+1; its positive output at most E(f)+E(g)+1.
Each is bounded by E(1+|f|+|g|). This bound is independent of the chosen
ordered binary association. Substitution of ones does not increase |f|.

For h of actual level m and n=lv(X)+1,

    S_X(h) ≤ 2^n Σ_{i=0}^m (2^{|h_i|}-1).

Its zero output has S_X(h)·(|(P_0 h_0)_0|+1)-1 nodes. A positive output
through n has at most Σ_i E(|h_i|)+m nodes. Higher outputs are unchanged.
For the box, its finite downward recursion gives the exact node recurrence
`|h_i|=|h_{i+1}|+|f_i|+|g_i|+2` for 1≤i≤n; its scalar output is the
chosen finite tail and a single primitive Psi node. Binary-sum association
does not affect these node bounds. Type levels, these displayed integers,
and source-tree recursion therefore supply a computable finite bound for
every generated original-source tree. No evaluation of ψ is required to
construct an assignment tree or its size multiplier.

## 4. Domain, norm and substitution

`WEAK-LEMMA-AND-NORM.md` proves the corrected scalar weak lemma, domain
closure and bounded-norm preservation. The proofs use only arities,
positive multiplicities and source primitive constructors. They apply to
every ρ. Natural sum's associative value and additive norm make the
particular parenthesization irrelevant *within these proofs*, which do
not assert that subsequent syntactic partials see identical input trees.

The box domain and norm estimates use interpreted finite sums and exactly
the published primitive constructors, so their value-level proofs have
the same scope for each ρ. Out-of-range operands are neutral comparison
zeros rather than new actual coordinate nodes. The zero-free, actual
coordinates are consequently in the published C classes and have bounded
norm by induction on original-source construction. For lambda, apply the
proved norm result to δh and substitute the all-ones vector into h;
componentwise addition preserves bounded norm since N is additive and
each scalar coordinate is its own finite norm.

Every partial output is X-free, by induction. A substitution of an X-free
vector for a different name preserves exactly which original nodes are
X-free and the tracked active-variable leaves. Therefore it preserves
s_X(h) and S_X(h), and its action commutes with the partial and abstraction
recursions. This is the source's Lemma2.20 with a literal ρ-commuting
reading. The policy's independence from operand names and internal content
is essential here. Alpha-renaming commutes for the same reason.

## 5. Uniform actual-source forward translation

For every fixed admissible ρ, let A be a literal original-T source all of
whose free term names have ground type. Its final positive coordinates
are closed and effectively evaluable. Its scalar coordinate translates
effectively, valuation by valuation and preserving shared names, into
positive-natural variables, positive constants, addition and fixed unary
heads

    h_lambda(t)=ψ(lambda+t),  lambda=ω⊗c>0, c closed.

Internal binders, higher types and recursors are allowed. The statement is
about the original syntax, not arbitrary annotated T′ recursor histories.
It is uniform in a supplied computable policy, but it does not erase ρ
from the target comparison problem.

Proof. Use simultaneous induction on generated assignments and partials.
The stronger syntactic invariant is that every positive generated field
contains only positive-index variable components, positive constants,
Add and the graded ExpProd constructor. In particular it contains no
component of index zero of *any* name. Prime clauses have this property.
Positive box fields use only positive inputs and preserve it.

For a positive partial input a whole-free diagonal output retains that
positive input and adds One; other outputs are One. A tracked variable
has constant outputs. Active Add and ExpProd cases preserve the invariant.
For a scalar input, any positive output is One in the whole-free and
tracked-variable cases. Active sums recurse. The scalar collapse case
adds a positive-head partial and a positive output of its scalar tail.
These are exactly the two simultaneous induction hypotheses. Repetition,
all finite sums and role-based padding preserve this invariant without
normalizing any operand. Abstraction also removes every component of
its bound name; its retained input has that name replaced by ones.

Thus the final positive fields mention only positive components of free
source names. There are none when all such names are ground. Their closed
values can be computed by the closed ordinal algorithms of paper05.

In any generated scalar field, variables are ground components, other
leaves are positive constants, and the possible constructors are Add
and Psi. Each Psi head belongs to the positive invariant. Once the free
names are ground and bound names have been removed, each such head is
closed, including heads in scalar partials. It is positive by the zero-free
graded domain, so λ=ω⊗c is a nonzero limit. Replace that literal collapse
node by the indicated unary function of its translated tail. The numerical
multiplicities S_X(h) are already fixed integers from the source trees;
expand them as repeated additions. This algorithm preserves every shared
valuation and does not introduce an extra independent input. ∎

The invariant is for generated assignments. C_i^X also allows promotion
of a whole-X-free scalar into a positive grade, and arbitrary members of
that ambient class need not satisfy the stronger invariant.

## 6. The two positive subclasses

For every ρ the following consequences of the same induction hold.

* With no recursor in the source, all final positive coordinates are
  finite. Only the recursor prime can introduce ω into a generated
  positive field. Once bound names have been removed, Add, ExpProd on
  finite inputs, and every positive partial clause preserve finiteness.
* If every internal type and subtype has level at most two, coordinate
  two has no grade-three exponent input. It is generated from ω and
  finite constants by sums, hence is of form aω+b. Coordinate one is
  generated by sums and ExpProd with exponents of this form, and
  `2^{aω+b}=ω^a·2^b`. It therefore belongs to N[ω]. Multiplication
  naturally by ω yields each direct scalar index below ω^ω. Bounding
  only the output type would not suffice.

The witness in `GENERATED-WITNESS.md` lies in both subclasses. The
subclass claims do not imply policy independence within them.

## 7. Soundness scope of this repair

The forward translation is an exact semantics-preserving translation of
each explicitly parsed zero-history assignment. Its graded domain and
norm estimates are paid below, including the source's false strict lemma.
This is enough to repair the paper05 translation and evaluation claims.

The published source's reduction soundness is about assignment
*derivations with histories*. It is not the assertion that these fixed
zero-history values strictly decrease on every reduction. Output-sum
association changes no value in the fixed-input inequalities used there;
the corrected weak lemma and bounded-norm supplier remove the specific
strictness error identified here. Nevertheless this note does not claim
to have reverified every appendix bound, every extended-T′ annotation
condition, or the entire original termination proof. Historical uniqueness
of an unspecified convention remains unproved and must not be cited as a
supplier for a convention-independent comparison question.
