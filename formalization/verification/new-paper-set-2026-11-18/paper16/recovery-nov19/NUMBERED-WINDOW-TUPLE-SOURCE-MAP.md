# Paper16 numbered full tuple: source-first exact comparator

Status: frozen proposal, offline only. No proof, native preflight,
source-edit authorization, or register change is claimed.

## Original source and ordering of work

The current statement is `lem:tuple-simulation` in
`16-persistent-marking-termination-ordering/sections/ordinals.tex`, at
the finite-budget subsection, with the raw rules and finite arithmetic
universe at the start of that file. `NUMBERED-WINDOW-TUPLE-FROZEN.json`
pins that manuscript, the actual old symbolic syntax, typing and
signature helpers, and four proposed new module sources. No legacy theorem
status is reused.

Of the four open numerical statements, this is the smallest whole
numbered endpoint. Full `lem:window-locality` also quantifies all terms
and side witnesses in **every literal six-sort finite original derivation**,
and the later constructed numerical intermediates, not just the tuple path.
The observation-closure endpoint cannot pay it: that is restricted to
reachable comparisons of one input pair and to its finite observed
context apparatus. To represent *every* original derivation faithfully,
use actual finite data certificates with only the six original judgment
sorts; `ExtendedTree` has extra marked-target/list constructors and is
not by itself an original-certificate substitute. A Prop proof-object
index alone does not distinguish separate literal derivations.

`lem:positive-simulation` additionally needs the full finite witness
recursion, consistency of all path intermediates, computable budgets,
finite equivalence and positive strict paths including lowered marked
sources. `lem:arithmetic-accessibility` needs actual internal `ID_1`
proofs in one numerical universe of all finite contexts, a path/quotient
arithmetic carrier and separately tagged positive I/J operators. A Lean
`Acc` theorem, interpreted postulate, or old fixed-context result does not
pay that endpoint. These three are not included in this proposal.

Historical Paper06 suppliers inspected: `NumberedRewriteSyntaxDefinitions`,
`NumberedRewriteReductionDefinitions`, `NumberedRewriteApplicationTargets`,
`NumberedFiniteUniverseDefinitions`, `NumberedDerivationSimulationTargets`
and `ID1Completion/ContextUniformTargets`. The old typed numbered
abstraction/beta cancellation and finite-numbered whole-tuple proof are
useful proof patterns. But the old term/type/context/precedence interface
differs, the old finiteMark expressly rejects an already-numbered head,
old raw syntax has no exact new lowering rule, and its raw reduction stack
imports Mathlib (outside the present core gate). The old Section06 target
files, Lean objects and proof status remain untouched.

## Rule, type and shape correspondence

- `NumberedWindowSyntax` uses the actual Paper16 `Ty`, `Head`, globally
  typed free names and de Bruijn bound indices. Ordinary head constructors
  implicitly carry omega; strictly finite labels are actual Nat fields.
  The original head and ordered base/extras coexist with current output
  type, so retyping does not erase a head's declaration. Auxiliary
  application is separate from `Head.app`, which remains a literal
  ordinary or numbered original head. Building the auxiliary application
  spine is not a replacement for `Spine.apply`.
- `NumberedWindowDomain` uses the same fixed finite list of types,
  subtype closure, and fixed ranked signature. Every type annotation
  and binder lies in the window; every original admitted head retains
  its declared argument and result types, including a retyped owner.
  Auxiliary contexts have the actual function and argument types.
  Symbolic admissibility uses original declaration-retaining support,
  neither the ordinary-only support projection nor decision port guards.
- `NumberedWindowRules` retains each printed raw rule: mark omega to
  any finite label, literal successor-label decrement, actual selected
  base or extra occurrence with the entire tuple of same old owner copies,
  precedence Copy, equivalent-head primitive strict Stat, abstraction
  and beta, and nonbottom-to-bottom. Copy and Stat retain the target's
  declared head-window guard; the typed `WindowStep` guards both terms,
  not only the marked output type. Primitive replacement retains equal
  original occurrences and permits deletion; every insertion is an omega
  mark or actual strict finite decrease (through the same initial lambda
  spine). There is no label-zero reuse; primitive finite decreases do
  not add a new direct raw skip edge. Lambda and original base/extra
  contexts are present. Auxiliary application closes **only** its
  function position. Bound-index zero in `openNumbered` is the alpha-fit
  fresh binder and shifts the old base and extras first. Beta uses the
  same nearest-binder-first, capture-avoiding block and ordered append
  convention as the original syntax, extended structurally to auxiliary
  bottom/app. The relation `WindowPath` permits zero steps but requires
  typed admissibility of every visited term in this same universe.
- `Realizes` follows precisely the original shape and retained lists:
  numerical head labels are omega at symbolic ordinary heads, and each
  symbolic mark has a finite label at least the given threshold. No
  auxiliary bottom/app exists in a realization shape; it may occur in
  raw auxiliary syntax or the start/path. `RealizationInWindow`,
  `RealizationWeakens`, `RealizationShift`, and
  `RealizationSubstitution` are separate supporting contracts, not
  numbered locality.

## Exact full-tuple endpoint

`WholeTupleSimulation` quantifies every finite binder stack, the fixed
subtype-closed window, original well-typed, signature-valid and admissible
inputs, the actual original typed call and equation
`Spine.apply q args = some r`, and arbitrary numeric realizations of
both the source and all arguments at **n + args.length + 1**. It concludes
the existence of the actual whole auxiliary application start term and
a window-preserving finite raw path to a realization of **that same r**
at n. There is no added closed-syntax, ordinary, head-only, fixed-point,
currying, source comparison, or enlarged-window premise.

The finite stack Γ is deliberately arbitrary, without a check that every
ambient stack entry is in K. This is stronger than considering only
contexts whose declared entries all lie in the source window. A variable
that actually occurs carries its recorded type in the syntax and is
looked up in that same Γ; symbolic support / numeric `InWindow` require
that type to lie in K. Thus any outside-K entries in the ambient stack
are unused, and no outside-K term, occurrence, requested application
domain, or path node is permitted. In particular the proposed theorem
specializes to every finite context in the literal arithmetic universe,
without silently limiting context size, fresh extensions, or free names.

Case plan, before proofs:

1. Empty tuple: the original call returns its exact source literally; the
   numerical start does too. Threshold weakening and actual window
   admissibility give the zero-step path, including a literal variable.
2. Initial original lambdas: take beta steps in the actual numeric
   application spine, using function-side lifting through remaining
   arguments. Track the prescribed simultaneous block of already consumed
   original binders and realized images. If the tuple ends here, the
   result is exactly the existing substitution on the residual syntax.
3. A symbolically original variable head with an unconsumed argument
   cannot be a successful `Spine.applyAux` branch, even if a consumed
   binder's image happens to be functional. Do not rescan a substituted
   numerical variable image to manufacture a new successful branch.
4. At an original functional ordinary head with r remaining args, one
   omega mark chooses a finite label at least n+r, then r abstraction/beta
   pairs append the numerical arguments in the same order while decreasing
   the leading label once each. Type suffixes are actual original
   proper-arrow suffixes; original base declarations stay present.
5. At an original functional already-marked head, retain its available
   finite label and take the same r abstraction/beta pairs; keep its
   existing extras before the appended tuple. Existing subterms retain
   their thresholds. In either head branch r≤args.length, hence the
   uniform sufficient **length+1** bound accounts for all actual units
   without claiming it is the minimum.

Proof dependencies to pay separately: joint realization type/support
transport, threshold monotonicity, shift/substitution compatibility,
actual full auxiliary spine typing/congruence, numerical shift/cancel beta
for appended owner arguments, work on the exact original `applyAux`
protected prefix, and assembly. None requires old marked comparison
transitivity, a source-size bound, or a semantic oracle. No proof should
start before independent review of the frozen source endpoint and
unchanged core preflight.
