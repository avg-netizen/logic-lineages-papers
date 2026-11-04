# Primitive-recursive existing raw numeric evaluator

This component supplies an effectivity step toward paper09 hardness.tex lines 316–319 using the finite-coefficient identity corresponding to foundations.tex lines 268–277. It does not change the source assignment or ordinal collapse semantics.

The target is exactly ParametricOmegaFreeEvaluator.evaluate, jointly in control index, finite numeric environment and raw syntax code. Joint Primrec H plus StrictMono and identity majorization of every section justify the actual collapse branch through ParametricPairValuePrimitive. The unchanged indexed raw fold is primitive recursive by OrdinalSyntaxPrimitiveFold. No finite-code restriction is needed for the numerical PR statement.

Raw behavior is unchanged: the leaf returns one only on code 1, looks up the environment with default zero on tag 3, and returns zero otherwise; internal tags 4/5/6 perform addition, 2^left*right, and actual finite-pair collapse. Omega and malformed inputs retain existing raw behavior, not an asserted ordinal semantic interpretation. Previously accepted semantic calibration applies only with omega-free syntax and the exact environment lookup premise.

FixedGammaPrimitive specializes to each fixed b and index zero. Sectionwise PR of Gamma is not upgraded to joint-in-b PR. Whole-source Option evaluator composition, input-independent iteration counts, runtime complexity and source-register/export claims remain separate.
