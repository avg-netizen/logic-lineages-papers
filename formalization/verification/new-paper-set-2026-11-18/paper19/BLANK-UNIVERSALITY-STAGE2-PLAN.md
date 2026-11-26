# Stage two: same-enumeration blank universality

Supporting scope for current19 control-sensitivity.tex's effective enumeration and undecidable blank halting. No full comparison hardness credit.

The concrete translator already lands in the EXACT accepted enumeration: `translate U e = PredictionUniformBinaryCompiler.compile U (normalizedIndex e)` produces a Nat code decoded by the same `decodeTable` as `program`. Work alphabets vary as Fin(width p); input and readout are binary. Do not describe this as a two-symbol work alphabet.

Propose seven exact supporting contracts in two bounded stages:

1. Literal primitive-recursive normalization c↦zero∘c∘zero, including its exact evaluation at every input and primitive-recursive normalized index.
2. Actual terminal-symbol validation for compiled tables: every terminating actual configuration has a binary head, and raw machine-evaluation domain equals binary readout domain. This prevents a hidden loss of halting when a nonbinary symbol is rejected.
3. A genuine fixed universal Turing.ToPartrec.Code U with primitive-recursive translate U and exact blank Halts(translate U (encode c)) iff (c.eval 0).Dom, for every Partrec code.
4. Actual blank Halts is not ComputablePred, derived from the standard halting problem through this actual translator, not a new premise.
5. Literal input specialization specialize c n = c∘const n is primitive recursive and has exactly c.eval n at every ignored input.
6. One actual U translates every pair (c,n) primitively recursively into the same blank-table enumeration, with exact halting domain equivalence.
7. For every genuine REPred P, a primitive-recursive reducer f with P n iff actual blank Halts(f n), plus ManyOneReducible. This does not assume P has an already-supplied machine code; code existence must be discharged through the real Partrec representation theorem.

The proofs may be thin current-source aliases only after exact independent freeze/source matching, with fresh complete recursive native evidence. First request bounded target-only import preflight because the compiler/evaluation transport closure is substantial. Divide blank-reduction4 and universal-specialization3 gates if necessary, keeping all endpoints source-exact. Any resource stop is preserved and reviewed; no cap relaxation or blind retry.

Subsequent actual gamma parity/nonperiodicity will use this SAME independent Halts and boundedH. Full source Pi01 completeness still separately needs actual restricted typing, addition/constants/S graph, compiler/collision, effective canonical evaluation/coRE and genuine source-DAG accounting.
