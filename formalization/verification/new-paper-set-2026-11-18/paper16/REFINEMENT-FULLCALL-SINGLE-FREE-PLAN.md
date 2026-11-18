# Smaller symbolic route: one fresh free argument at each recursive lambda

This refines the all-at-once symbolic tuple draft, without general staged
application or its false associativity. Freeze and prove three exact raw
helpers before use:

1. Success existence of applyAux q args values is independent of values. Its
branch choices and consumeTypes checks use q/args only. Values affect output
substitution only. Thus ∃r,aux q args vs=r implies ∃r',aux q args ws=r'.
2. For any values vs, depth d and literal free z, prove the actual block law
   substitute vs d (substitute [z] (d+vs.length) q)
   = substitute (vs.append [z]) d q.
   This is NOT general substitution associativity: the outer removed value is
   precisely a free variable, so no introduced lambda/head/capture is involved.
   The corresponding Args law is structural. All bound-index retained,
   in-block, exactly-new-slot and out-of-block cases must be paid.
3. Derive the exact free-opening full-call equality
   apply (lam σ q) (free σ x :: args) = apply (openBody σ x q) args.
   Prove it through applyAux with invariant
   aux (substitute [free σ x] vs.length q) args vs
     = aux q args (vs.append [free σ x]),
   using (2). A substituted original bound variable becomes a free variable,
   hence both branches still block nonempty remaining arguments. Arbitrary
   non-free inserted arguments are NOT allowed by this equality.

FullApplication then recurses on the actual argument tuple length. At lambda,
choose x fresh in both original terms AND every actual argument value. Existing
right full success, (1), and (3) give successful right call with a symbolic
first argument and the unchanged actual tail. Opening supplies refinement of
the two opened bodies. Recursion on the shorter tail supplies refined symbolic
outputs. Use (3) backwards only for this literal free argument to recover both
symbolic full calls.

Two one-name maps send free σ x to the respective original first arguments and
fix everything else. Freshness fixes the original lambda terms and all tail
arguments. Actual forward full-call covariance maps both symbolic full calls
to the original full calls. Full two-environment refinement substitution maps
the symbolic output refinement. Determinism identifies the right output with
the supplied r. This does not infer staged equality for arbitrary first values.

At head/marked roots the actual one-shot whole remaining tuple append is proved
by genuine append/omission refinement and already-checked transitivity for old
whole-owner extra suppliers. Variables contradict actual right success; empty
calls return their original terms. All tuple typing and annotation equalities
are proved internally from the frozen endpoint's hypotheses.

The known non-free λx.x/[S,y] counterexample is unaffected: helper (3) requires
the inserted value to be literally free. General associativity remains false.
