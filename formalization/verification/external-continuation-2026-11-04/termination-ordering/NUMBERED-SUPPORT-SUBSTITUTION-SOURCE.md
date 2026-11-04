# Predicate-respecting substitution preserves support

Draft for review; no proof/export. Binder-aware structural support supplier for paper 06 beta/fresh-context reasoning.

Both targets assume arbitrary typed predicates P and Q, source term/tuple support under P, and the explicit environment condition that every P-allowed variable is sent to a Q-supported term. They conclude Q support of the literal substituted term/tuple. This is forward only; substituting bottom for a variable can erase support information, so no converse is asserted.

Under lambda, lifted predicates and lifted substitution are used. The bound here is mapped to var here and allowed. A there variable maps to the weakened original image; the accepted renaming pullback identifies its lift-Q support with the original Q support. Complete ordinary/numbered bases/extras and both application components are retained. No non-bottom, injectivity, finite-window or precedence premise is required.

No beta-specific step, general step support preservation, relation image closure, Acc/C stability or ID1 claim. Prior accepted files unchanged.
