# Literal comparator, occurrence witnesses and presentation bridge

## Source and boundary

Authoritative clauses are foundations.tex (fixed finite ranked signature,
literal native/app declarations and precedence classes) and ordering.tex
(occurrence multiset definition, eight weak clauses and Strict). The current
Spine carrier/typing/call/mark/free-substitution operations remain unchanged.
Neither the old Paper06 relation nor its theorem status is imported. No
comparison oracle or assumed closure law is introduced.

## Finite signature and precedence

Represent a signature by a finite ordered table of pairs (ranked name, arity),
with distinct ranked names. Table order is the chosen strict total precedence,
from smaller to larger; arity is fixed by its table entry. A ranked raw Head is
admitted exactly when its pair matches that unique entry. Native constants and
typed application heads are always admitted, and ranked names remain a separate
constructor from both. Define concrete class ranks: application class 0,
native class 1, and admitted ranked head at table position i class 2+i.
Equivalent admitted heads have equal class rank, strict precedence is strict
Nat rank inequality. Thus all native type instances are equivalent, all typed
apps are equivalent, and distinct ranked heads are strictly ordered. Invalid
raw ranked nodes are excluded by a recursive signature-valid predicate, not
assigned arbitrary usable ranks. No assumption of a generic relation's
well-foundedness substitutes for this concrete construction.

## Occurrences, not sets

Use actual Args positions. Define At xs i x, removal of one selected occurrence,
and an order-preserving split of a list into retained and removed subsequences.
These are finite inductive witnesses, not membership in a deduplicated set.
A weak matching removes exactly one target occurrence for each source occurrence
and has one equal-typed weak premise, giving a permutation/bijection even for
repeated equal terms. Strict replacement splits both source and target,
requires a nonempty removed source list, weakly matches retained lists, and
covers each new target occurrence by a strict premise from some removed source
occurrence. Coverage may reuse a source occurrence and may leave sources unused.
The empty new target list is allowed. Extras never enter the base multiset test.
These witness relations are mutual with W and S where required for positivity.

## Fresh opening, not a silent alternate binder rule

Use actual opening of a locally nameless body with typed fresh free variable
x via the checked one-element simultaneous substitution. Abs opens both bodies
with the same fresh typed name. FAbs appends that free variable to the owner's
existing extras and compares it with the opened target body. Freshness excludes
the free typed name from both original endpoints; ordinary outer bound indices
are retained correctly by the opening operation. Do not simply replace these
clauses by an unexplained relation in a pushed context.

Compute finite free typed names and provide a concrete fresh-name witness from
a bound on the finitely many numeric names. This is required for reflexivity,
not assumed as an oracle. Prove opening typing from actual parallel typing.

## Actual comparison rules

W and S range over signature-valid, typed auxiliary terms at equal outer type.
Each constructor retains the printed shape and exact side conditions:
Var (identical typed variable), Abs (common fresh opening), Fun (equivalent
heads, equal result types, occurrence matching), Put (literal empty-extra mark),
Select (selected base or extra occurrence, actual full original-spine call on
owner self-copies at the selected arrow domains, successful result W target),
FAbs (fresh opening and append exactly one free variable), Copy (strict head
precedence plus W premises from retyped whole owner to every target base),
Stat (equivalent head plus base-only occurrence strict replacement and the same
whole-owner premises). Strict requires actual successful persistent mark then W.
Self-copies change output annotation only, leaving original head/base/extras
fixed. Domain decomposition and result suffix are computed from the selected
type; no arbitrary supplier is accepted. Signature/typing proofs must be either
actual constructor premises or proved consequences, never informal claims.

## Required presentation bridge

The manuscript explicitly permits typed de Bruijn representation but identifies
only bound renaming, not beta/eta or application rearrangement. We must connect
our witnesses to that precise carrier. Introduce a typed-name raw syntax (or
reuse the old named syntax only after fixing its type/name environment mismatch),
with names the pair (Ty,Nat). Encode a named term by looking up the nearest exact
typed-name binder in a stack, preserving every head declaration, base position,
extra position and application node. Decode locally closed DB terms by choosing
fresh names. Prove encoding respects fresh bound renaming, decoding/encoding
roundtrips on scoped terms, and the common-fresh-opening correspondence. These
are proof obligations, not postulated axioms or a definition that silently
asserts the correspondence. The earlier Nat-only shadowing context is not this
bridge. Until these checks are completed, relation results are labeled auxiliary
locally nameless results and not numbered manuscript proofs.

## Staged exact targets

First: finite signature admission/unique arity and actual precedence cases;
occurrence witness bookkeeping; opening/scoping/typing and fresh-name witnesses.
Then freeze the literal mutual relation after independent clause-by-clause
review. Prove targets ordinary by joint derivation induction; strict inclusion
using successful mark shape and the actual Abs/Put clauses; ordinary reflexivity
with identity occurrence matching and concrete fresh opening. These are the
three constituents of lem:elementary, but do not promote the manuscript label
before the presentation bridge is proved/reviewed. Structural substitution and
context closure follow using already checked successful mark/call covariance,
with ordinary signature-valid images and occurrence multiplicities preserved.
Only then approach the printed finite-support saturation/decidability argument.

Definitions/endpoint freezes follow review, not this plan alone. No compiler
queue is requested until concrete reviewed proof packets are ready.
