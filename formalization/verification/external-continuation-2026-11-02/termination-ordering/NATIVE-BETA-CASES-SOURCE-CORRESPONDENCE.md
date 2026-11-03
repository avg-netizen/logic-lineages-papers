# Original beta and native cases — exact confined orientations

Source paper06 `lem:betacases`, lines457–473. The beta target quantifies every ordinary body and argument at arbitrary scope/type, retaining the actual typed `Term.substitute (Substitution.single arg)` contractum. The two case targets retain the original curried Dτ u A B with every ordinary test u and either original branch, exactly the stronger comparisons proved in the manuscript. Instantiating u=0 for the first and u=S n for the second gives the two original native case rules.

All three conclusions use the existing actual Strict on marked embeddings together with literal typeSupport inclusion. No beta-normality, closedness, a preselected argument witness or generic substitution-stability premise is added. Arbitrary ordinary source substitution instances are included in the quantified body/argument/test/branches; a later all-reductions theorem will assemble contextual closure and recursor rules separately.

The beta proof uses original outer marking, zero-argument Select of the original argument, proved ordinary-template grafting with the self-copy as marked input, and original simultaneous lambda-spine consumption. It does not substitute a semantic lambda operator or assume transitivity. Exact support is to be proved using actual occurring variables; unused context variable types must not be inserted into the source support to make the claim hold.

Case branch B follows outer zero-argument Select. Branch A follows one simultaneous Select of the inner application, then zero-argument Select of A. Complete all three targets before full `lem:betacases` adoption; no stable-pair/well-foundedness claim is made.
