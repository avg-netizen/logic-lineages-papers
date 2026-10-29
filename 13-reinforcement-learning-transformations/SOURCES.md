# Sources and transformation contract

Samuel Allen Alexander and Arthur Paul Pedersen, *Representation and Invariance in Reinforcement Learning*, [arXiv:2112.07752v5](https://arxiv.org/abs/2112.07752v5), 11 August 2026, supplies Definition 2 and the four frameworks in Definitions 6–9. The paper uses finite alphabets, integer rewards including 0 and 1, rational behavioral probabilities, all history functions, and finite limiting expected total reward against every policy. It uses the surrounding alternating percept-first process directly to define finite values.

The printed faithfulness clause compares two agents in the **same** environment. No injectivity, computability or preservation of cross-environment scores is added. This exact scope is essential: the positive environment map selects among three source environments using the sign of two target values.

The previous public [counterexample note](https://github.com/avg-netizen/alexander-open-problems-results/tree/main/05-rl-transformation-counterexample) contains the two-point collapse idea and the distinction between same-environment and cross-environment comparison. The new manuscript credits that note but includes a complete independent presentation. It extends the construction to all positive cells and proves all remaining negative cells by a scripted separator and an explicit rational behavioral mixture. The source's mixture results provide background; the necessary identity is proved here.

The finite matrix example proves failure of the naturally composed maps to preserve both nontriviality conditions. It does not claim that those matrices rule out every alternative map. The lattice argument concerns the explicitly stronger cross-environment contract; it is not used in the four-framework classification.

Earlier historical twelve-framework versions, effective or injective translations and normalized-reward variants are outside scope. The current source definition and every local proof used for the classification are printed in the manuscript.
