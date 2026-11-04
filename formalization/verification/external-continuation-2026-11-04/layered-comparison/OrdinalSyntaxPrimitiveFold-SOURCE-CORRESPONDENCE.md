# Indexed primitive-recursive existing ordinal fold

This is a representation/effectivity supplier toward paper09 hardness.tex lines 316–319, not a new source theorem or evaluator claim.

The target uses exactly OrdinalSyntaxComputableFold.indexedFold, hence the unchanged OrdinalSyntax.fold. Tags 0, 1, 2, 3 and 7 call the supplied leaf on the entire raw code. Tags 4, 5 and 6 unpair code/8 and call the supplied branch with code%8 and both recursively computed results. The exact previously accepted raw recurrence and strict child decrease are retained, including all malformed/raw inputs. No typedness, omega interpretation, or finite denotation is inferred from this numerical fold.

For any first-order Primcodable parameter P and result A, joint Primrec leaf and joint Primrec branch imply joint Primrec of the existing indexed fold on P × Nat. This is uniform in the explicit parameter, not a claim that arbitrary sectionwise PR functions are jointly PR. Strong recursion must be implemented using a primitive-recursive table of smaller codes; the proof may not merely appeal to well-founded termination or the prior Computable result.

Omega-free evaluator PR, whole-source assignment composition, actual Gamma specialization, joint-b control PR, quantitative size/runtime and source-register changes remain separate. No manuscript/export changes.
