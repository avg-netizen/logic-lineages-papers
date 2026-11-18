# Actual protected-spine interpreter: concrete recursor design for review

Source: decision.tex, Structural interpretation and the operator, lines 108–176; original syntax and application are SpineSyntax.lean Expr/Args/applyAux/apply. StructuralActions8 is supporting infrastructure, not this lemma.

## Representation and scope

Use the original Expr and Args, the actual retained family M, actual hereditary codes, and typed finite free assignments plus a nearest-first typed bound-value stack. Values retain their type and actual context; weakening maps actual codes with descriptor.restrict, never reuses an index across contexts. Missing or ill-typed assignments are explicit invalid raw branches, with absence of those branches proved for well-typed source environments. An unassigned literal free name denotes the actual variable value (matching weak observation, no strict observation, whole-bottom nonempty tables). An assigned free name denotes its assigned value, including that value's full table.

The semantic output initially is the existing Value record, with actual finite-schema encoding only after Valid is proved. There is no interpreter callback supplied as a hypothesis. Base/extras are interpreted by the actual Args recursion, preserving positional bases and converting extras to the existing typed down-set. Marked nodes consult the given M at their original head/output/context and interpreted bases/extras. Ordinary heads construct the literal Fun test on target head arguments plus the marked-counterpart weak test; strict bits are exactly the counterpart weak bits. Fun uses finite positional matching, not equality of an unordered base set. All source head/declared-type inventory premises are discharged from the source-universe packet at final source instances.

## Protection belongs to one original call, not permanently to values

The helper carries a nearest-first prefix of values for lambdas consumed during THIS original-spine scan, separately from the ambient bound stack. Equivalently it carries a consumed-prefix count together with the concatenated stack. The prefix origin, not the shape or identity of its assigned value, determines protection.

With a nonempty remaining tuple, a bound index in that consumed prefix returns the whole residual bottom, even if its assigned value is a lambda or head. A bound slot from the pre-existing ambient substitution, or an assigned free variable, reads its assigned value's one full remaining-tuple table. A literal unassigned free variable has bottom nonempty tables.

CRITICAL end-of-tuple rule: when the tuple becomes empty, interpret the residual term under the updated value environment, forgetting the current scan's protection markers. A later independent call on that interpreted residual starts a NEW scan with an empty protected prefix. Retaining old protection in a residual lambda would incorrectly strengthen blocking and conflate a full original call with staged calls. No theorem equates those two operations.

## Actual equations and termination

The simultaneous implementation has Expr interpretation, Args interpretation, and a NONEMPTY original-spine helper. Interpretation of a lambda's nonempty application coordinate consumes the first correctly typed argument and calls the helper on its original body if arguments remain, or ordinary interpretation of that body if they do not. Thus it does not call a same-source helper which can call interpretation back on that source.

The helper's lambda branch consumes one argument and descends to the original body; its head/marked branch interprets original base and old extras under the updated environment, then appends ALL remaining tagged arguments simultaneously, computes the residual type from the whole original arrow prefix, and consults the SAME M. The free/ambient-bound branch performs one full table read; the protected-bound branch returns whole bottom. It never inspects a replacement value's syntactic head.

Termination uses the actual Expr/Args mutual structural size: recursive interpretation occurs only at original bodies/base/extra children, and helper lambda recursion strictly descends the original body. The nonempty helper design avoids the same-size interpretation/helper empty-call cycle. No source-size bound or arbitrary recursion oracle is a premise.

## Lambda observation fields and finite freshness

Weak and strict fields inspect only actual lambda observations with the matching domain. Open the target's actual body at an available typed port, and interpret the source body with that literal port value pushed into its bound environment. Spare-slot existence comes from the observed lambda's budget, not an assumed fresh port and not the source lambda's depth. Matching lambda bits remain separate from tuple behavior.

A canonical opening choice is only an implementation choice: prove independence via finite typed renaming of actual observations, environments and M coordinates. Existing used ports and free-name inventories must be fixed or explicitly transported; both endpoints' relevant finite free-name support must be included. Naturality must compare opening choices after extension, where a formerly unused slot can have become occupied, rather than assume the same canonical slot remains available. Out-of-budget/off-schema raw fields may be assigned deterministic defaults, but no actual observation may be excluded by that convention. No new observation context or infinite-support fresh-name assumption.

## Proposed exact staged contracts, before any definitions/proofs

1. Actual recursor equations on all five Expr constructors and both Args constructors, including empty-call reset and original protected-prefix blocking, plus literal whole-list head append and original type consumption. Freeze executable definitions and exact equations together after review.
2. Derive typed output validity and inventory/support preservation for actual environments. This includes lambda fresh-opening coherence, every optional encoding/output success and whole-bottom branches. Any local type/port invariant must be discharged at the source-level endpoint, not inserted as a new hypothesis in the printed lemma.
3. Monotonicity in M and actual typed environment values, and weakening at every well-formed extension, proved simultaneously over the genuine source/helper recursion. Head cases use (C), assigned-variable calls use (N), protected cases whole bottom. No generic assumed monotone semantic function.
4. Capture-avoiding substitution correspondence, with actual bound-stack shift/lookup and free-substitution composition; closing/opening bridges already proved are reused where applicable. Freshness and environment finite support remain explicit proof obligations.
5. Full concrete-substituted application correspondence: for environments interpreting actual finite concrete substitutions, compare the helper against apply of that substituted original source, with both success and undefined cases. Distinguish consumed original binders from substitution images; unprotected free substitution can turn the previously undefined literal-variable call into success. Preserve this direction, and do not prove failure transport from the unsubstituted source or staged associativity.

The original four positive constructor tests and previous-M tuple outputs follow as the next source stage, not a generic family wrapper. Their validity/(C) must precede encoding and the actual endomap/fixedpoint theorem. Adequacy remains separate.

Request: independently review this concrete simultaneous-recursion/protection/reset/freshness design before new definitions and frozen contracts.
