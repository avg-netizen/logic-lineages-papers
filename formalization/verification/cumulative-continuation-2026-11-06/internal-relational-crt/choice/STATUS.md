# Relational CRT choice supplier

The bounded compiler passed InternalRelationalCRTChoiceProof on candidate 02.
Receipt: build-reports/1794005210324965465-8.json (copied as receipt-02.json).

This supplier proves renaming and arbitrary embedded term substitution through the original relation, existential introduction and genuine fresh-variable elimination, and congruence transport retaining that relation. It does not prove the final relational bounded CRT target. The parent owns exact-target and axiom auditing and integration.

Candidate 01 failed only because a rewrite did not unfold a fresh-variable formula alias. Its complete source, output, and receipt are retained. Candidate 02 explicitly changes to the existing liftP alias before using the already checked freshP lemma.

No accepted source was edited, no axioms or admission shortcuts were added, and no publication was attempted. Compiler slot released after all compiler processes exited.
