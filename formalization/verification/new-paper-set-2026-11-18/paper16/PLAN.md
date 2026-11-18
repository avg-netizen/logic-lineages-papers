# Paper 16 source-exact port

Source: `16-persistent-marking-termination-ordering`, imported unchanged from
papers/ii5-explanatory-2026-11-17 at 17377d6d.

## Reuse and mismatch audit

The earlier Paper 06 source is not this relation. In particular a persistent
mark fixes marked owners; strict multiset premises may have marked sources.
A full original-spine application is not iteration of unary application.
The extended marked-target relation permits strict self-comparison and is
NOT a well-founded relation. The ordinary-final cut and conservative
elimination are obligations, not aliases to old stable-pair targets.
The first-order carrier is actual ranked ground nodes; native constants
remain nullary and application remains binary. Native type instances share
one precedence-equivalence class; application instances share another.
The confined type support retains native declarations after output retyping.

Existing syntax/coding/library proofs can be reused only after a literal
semantic match and dependency/axiom audit. No earlier checked numbered
statement is automatically credited here.

## First component: persistent marking (supporting, not numbered)

`Syntax.lean` supplies literal simple types, six head constructors (native
zero/successor/case/recursor, typed binary application, ground ranked), and
raw annotated terms. Base and extra lists stay distinct. `mark` only follows
the initial lambda spine; at a head it marks once, at an already-marked owner
it fixes all fields. `headmark` is total, leaving variable-ended spines fixed.
Frozen `MarkingTargets.lean` requests persistence, idempotence, successful
agreement, exact variable-spine failure, and outer-type preservation.

This first carrier uses names and allows raw ill-typed annotations. Its laws
hold uniformly on all raw trees and are equivariant in binder names. It is
NOT yet a completed alpha-quotient, typed substitution, or comparator. The
presence of arbitrary raw trees does not weaken these supporting laws, but
no theorem about the paper's typed relation is promoted from them alone.

## Next exact obligations

1. Typed binder representation, alpha correspondence, literal support/FV;
   original-spine simultaneous substitution with exact blocking behavior.
2. Original weak/strict finite-derivation relations, occurrence multiset
   matching (multiplicities preserved), and `lem:elementary`.
3. Support/substitution and contexts, free variables, then auxiliary extended
   relation, refinement, prefix escape, conservative ordinary-target cut.
4. `thm:stable`, exact ranked RPO restriction, literal five reductions.
5. Finite natural observation domains and exact full-tuple semantics; do not
   replace natural tables by unconstrained finite function tables.
6. Numbered relation, internal positive simulation and actual arithmetic
   accessibility; exact upper/lower height and finite-type iteration.

All target statements must be frozen before proof. No statement is checked
until native compiler, exact type aliases, actual axiom closure and independent
source/evidence review pass. Core-only imports are intentional for the first
component; they do not establish an aggregate build.

## Typed marking companion (draft, separate frozen target)

`Typing.lean` makes the named auxiliary typing judgments explicit. Each
ordinary head checks its original base list against `Head.arguments`;
marked heads check that same list and independently type every extra, while
allowing the output annotation specified by the paper. A binder shadows
its variable's context entry. `TypedMarkingTargets` separately freezes
annotation exactness and typed preservation for partial/total marking.
The ranked signature's name/arity consistency is still an external admitted
syntax restriction, not yet supplied by a finite-signature type. Since these
laws hold for every raw name/arity pair, they apply to any consistent fixed
signature, but this does not by itself formalize its precedence.

This is a presentation before quotienting by alpha; no substitution operation
or alpha-respectfulness proof has yet been supplied. Such a quotient bridge
must precede claiming the complete paper syntax/structural-stability theorem.
