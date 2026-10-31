# Source and proof guide

| Source | Use in this paper |
|---|---|
| Gonzalez, Rossegger and Turetsky, *Scott Analysis below the Vaught Ordinal*, [arXiv:2606.15205v2](https://arxiv.org/abs/2606.15205v2) | Question 2 asks about JEP for avoidance classes of finite order forests. Version-specific forest/embedding conventions are retained. |
| Goubault-Larrecq and Schmitz, *Deciding Piecewise Testable Separability for Regular Tree Languages*, [ICALP 2016, article 97](https://doi.org/10.4230/LIPIcs.ICALP.2016.97), Example 7 and Section 5 | Effective finite decomposition of a regular ranked-tree language's homeomorphic downward closure into regular ideals. Proposition 18, Fact 19, Lemma 20 and Theorem 23 supply the construction. The exact ordered ranked relation is stated in the manuscript. |
| Esparza, Ganty, Kiefer and Luttenberger, *Parikh's Theorem: A simple and direct automaton construction*, [arXiv:1006.3825v3](https://arxiv.org/abs/1006.3825v3), Theorem 1.1 and Section 3 | Effective Parikh/Presburger predicates for the finite grammars that track all binary associations and permutations. |
| Carter, *On the joint embedding property for cographs and trees*, [arXiv:2409.06127v1](https://arxiv.org/abs/2409.06127v1) | Related graph JEP work. No theorem from this preprint is a premise of the present decision proof. The separate source-repair notes explain the containment issue. |

The manuscript proves the graph-image transfer from tree ideals, exact canonical cotree state semantics, and deterministic Presburger inclusion and emptiness. In particular it does not equate graph JEP with JEP of all binary graph representations. The comparability-graph argument includes uniqueness up to order isomorphism and preservation/reflection of the existence of embeddings. A particular induced graph embedding need not itself preserve the order.

The width proof is given directly using binary refinements and leaf clusters. Its negative cases derive cluster preservation from saturated width rather than assuming root or meet preservation. The certificate proposition proves a host-size bound for each candidate pair; it does not invent an input-size bound for the first bad pair. The age construction uses JEP and heredity, without assuming amalgamation or claiming homogeneity.

The repaired mathematical algorithm is not claimed to be an implementation or a Lean result. Bounded controls and exact source/review records are included under `repair/`. Independent human mathematical review and priority checks are still needed; document assembly checks do not supply them.
