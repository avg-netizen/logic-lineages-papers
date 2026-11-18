# Independent shift/substitution/insertion pre-scope

Approved for native checking as supporting raw locally nameless algebra.
All pins in SUBSTITUTION-FROZEN.json and INSERTION-FROZEN.json match the current
SpineSyntax and target bytes. No compiler run here. No source definitions or
frozen propositions changed by this review.

Seven SubstitutionTargets concern all actual Expr/Args constructors: shift by
zero, same-cutoff composition by addition (including recursive lambda cutoff
increments), empty simultaneous substitution, and preservation of the outer
recorded type by shift. These are genuine universal structural laws, but the
last only concerns annotations, not a typing judgment or full type soundness.

Three InsertionTargets concern the actual substitute function: insertion at
the start of a removed binder block lifts the first supplied value by depth;
indices below depth remain bound locally; passing one retained binder raises
the examined index and result by one. The last equation includes i<depth,
indices inside the substituted block and indices beyond it. For an in-block
lookup its two sides agree by composition of lifts; beyond the block, lookup
failure entails the length bound needed to commute subtraction and successor.
No hidden well-formedness or type premise is added; arbitrary values/rest are
retained. Inconsistent raw annotations are not asserted to be well typed.

These statements support the manuscript's capture-avoiding simultaneous
substitution implementation but are not themselves the full source theorem
that successful original-spine application commutes with substitution. They
also do not establish typed application correctness, alpha correspondence or
comparison preservation. Keep this distinction in all promotion/reporting.
Native exact aliases and recursive evidence remain required.
