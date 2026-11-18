# References, dependencies and retained corrections

Gunnar Wilken and Andreas Weiermann, *Derivation Lengths Classification of
Gödel's T Extending Howard's Assignment*, LMCS 8(1:19), 2012,
DOI 10.2168/LMCS-8(1:19)2012, identifies the original norm-controlled
setting. Wilfried Buchholz, Adam Cichon and Andreas Weiermann, *A Uniform Approach to
Fundamental Sequences and Hierarchies*, Mathematical Logic Quarterly 40(2),
273–286, 1994, DOI 10.1002/malq.19940400212, supplies historical ordinal
background. The exact maximum-predecessor algorithm, saturation, collapse
recurrence and complete count used here all have local proofs.

Stefan Kiefer, *Notes on Equivalence and Minimization of Weighted Automata*,
arXiv:2009.01217v1, 2 September 2020, provides the field-valued observer
context. The primary version's Sections 1–3 were inspected. The numerator
closure, coefficient formula and distinguishing-continuation theorem are
proved directly in this manuscript, without importing an unspecified
automata minimization result.

The source is entry 10 at public commit
4028a9e34506f4339af2992749464cf2d4d55eb9. Its independent standard-control
results are retained, and the shared numerical foundations are included
locally. The new complete-profile section explicitly proves closure under
both binary selectors, includes every pole, and states the scalar output.

The rewrite corrects the index of the finite coefficient in the first
polynomial of the transfer proof. It distinguishes the adjacent-input
surrogate G(u+1) from the actual next norm G(G(u)). It states eventual
finite cycling only for the finite-field inputs used here: a perfect
field alone does not make inverse Frobenius periodic. The concrete
family is proved to arise in an actual ordinal descent; a typed-source
adapter for arbitrary larger assignments is not silently assumed.

The unbounded exact period belongs to a selected residue tuple. It gives
a divisibility lower bound on a complete rational-state period. It does
not prove a selected scalar bit nonperiodic, show every numerator state
reachable, or decide the all-ground problem for the unchanged control.

The included finite checks compare partition coefficients, matrix outputs,
finite-field profile transitions, arbitrary binary pole transients, and
congruent growing-budget segments on their stated bounded ranges. Their
successful execution supports those finite interfaces only. The general
ordinal and quantified theorems remain hand proofs; no new formalization
target is marked checked.
