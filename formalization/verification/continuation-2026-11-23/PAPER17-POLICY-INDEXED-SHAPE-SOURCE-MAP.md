# Paper 17: a supplied literal-policy program at the actual macro dispatcher

The actual policy source is the ordered full binary shape selector indexed by macro site and arity, as in `sections/source.tex`. A supplied program index implements a selector only when its universal evaluation returns the actual tape code for every tag and arity. Every effective typed policy has such an index.

The joint partially recursive macro program uses the supplied index, exact tape decoding, and the existing syntax-preserving macro evaluator. Under the index premise, both directions of output membership follow from the literal equality with the existing macro. On arbitrary indices, macro divergence is exactly policy evaluation divergence; a returned `none` is a distinct, terminating macro result. No universal validator, indexed assignment/compiler, or promotion of any numbered theorem is asserted.
