# Ordinary finite-signature restricted simulation

The input syntax is the actual original Term over an arbitrary finite ranked
signature Fin n with its actual arity function. The executable symbol list is
List.ofFn id; the executable type window is literalTypes s ++ literalTypes t,
which lists the genuine endpoint type support including subtypes. No context
or normal-form restriction and no endpoint confinement hypothesis is added.

The first target derives subtype closure, both embedded original source/head
confinement facts, and both zero-label canonical translations' confinement.
The other two targets use actual original Weak/Strict derivations and produce
restricted paths between the fixed literal translations. Every boundary of
the produced path is confined to this same finite head/type window. Strict
paths have genuinely positive counted steps. Uniform certificate budgets are
removed from ordinary translations using proved unmarked representation
rigidity, not by discarding their label constraints.

This specializes chosen restricted simulation to finite ordinary inputs. It
does not establish finite primary-equivalence classes, least-code quotient,
numeric computable translation, ID1 accessibility, ordinal bounds or the full
paper simulation lemma. It does not change the original comparison or its
checked transitivity obstruction.
