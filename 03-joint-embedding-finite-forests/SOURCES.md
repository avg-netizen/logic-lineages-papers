# Source and proof guide

| Source | Use in this paper |
|---|---|
| Gonzalez, Rossegger and Turetsky, *Scott Analysis below the Vaught Ordinal*, [arXiv:2606.15205v2](https://arxiv.org/abs/2606.15205v2) | Question 2 asks about JEP for avoidance classes of finite order forests. Version-specific forest/embedding conventions are retained. |
| Carter, *On the joint embedding property for cographs and trees*, [arXiv:2409.06127v1](https://arxiv.org/abs/2409.06127v1), Corollary 1.5, p. 2 | Decides JEP for finite forbidden induced-graph families containing P4. The translated family contains both P4 and C4. |

The graph corollary is the imported algorithm. Carter's distinct rooted-tree maps are not identified with order embeddings. The manuscript gives a complete comparability-graph argument, including uniqueness up to order isomorphism and preservation/reflection of the existence of embeddings. A particular induced graph embedding need not itself preserve the order.

The width proof is given directly using binary refinements and leaf clusters. Its negative cases derive cluster preservation from saturated width rather than assuming root or meet preservation. The certificate proposition proves a host-size bound for each candidate pair; it does not invent an input-size bound for the first bad pair. The age construction uses JEP and heredity, without assuming amalgamation or claiming homogeneity.

The full Carter algorithm is neither reproduced nor independently implemented here. Independent mathematical review is still needed; manuscript assembly checks are not such a review.
