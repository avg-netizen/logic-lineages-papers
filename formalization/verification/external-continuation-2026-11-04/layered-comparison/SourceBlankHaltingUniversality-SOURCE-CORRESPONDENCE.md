# RE predicates reduce to the actual blank-table halting problem

This supporting bridge concerns paper09 hardness.tex lines 294–319, the effective machine enumeration and subsequent hardness/upper-bound argument. It does not identify time clocks of distinct machine representations.

Specialize c n is literally Code.comp c (Code.const n). Its evaluation on every input x equals c.eval n, and its constructor is primitive recursive jointly in the Code and natural input. The accepted validated blank-machine translator is composed with the exact encoded specialized Code. One fixed translator U works for every c,n, with halting equivalent to the domain of c.eval n.

For an arbitrary predicate P on Nat with REPred P, map its partial unit-valued recognizer to a partial Nat-valued recognizer, obtain a fixed Code by the existing Code.exists_code theorem, and use the preceding specialization. The resulting n-to-blank-machine-index map is primitive recursive even though recognizing P need not be total or primitive recursive. The code and translator are existential fixed parameters; no uniform algorithm extracting them from a proof of REPred is asserted.

REUniversality states both the exact primitive-recursive witness and the standard Mathlib ManyOneReducible relation. It concerns all RE predicates, not merely the generated source language. Complement transport, co-RE classification, Gamma language completeness, weak comparison, runtime correspondence and source-register promotion remain separate. No accepted source, translator, manuscript or encoding changes.
