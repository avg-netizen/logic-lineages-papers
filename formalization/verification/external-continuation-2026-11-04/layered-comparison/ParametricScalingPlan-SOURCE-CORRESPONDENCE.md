# Shared variable doubling for the fixed coefficient 2^e

Paper09 hardness.tex lines294–314 uses the fixed coefficient 2^e multiplying the variable expression 2t+C and counts arithmetic DAG size in the numerical index e. This component supplies only that bounded variable-scaling operation, for arbitrary input and output ports, with a continuation.

scalePlan zero emits one equality gate. At e+1 it binds one fresh ground child, recursively scales the shifted input into that child, adds child+child=shifted output, and shifts the original continuation once. No producer expression or continuation is duplicated. All gates are existing eq/add gates, so the supported actual Gamma compiler applies. Arbitrary-G EvalWith semantics is an arithmetic plan identity; actual Gamma realization uses proved primitive source equations, not assumed source arithmetic.

The exact plan metrics are 80*(e+1)+q.vertices, 10*(e+1)+q.equations, and 10*e+9+q.witnesses. The final compiler has at most that many source-DAG vertices, exactly that many equation pairs, and original context length plus the stated witnesses. This counts e explicit child binders and nine fresh auxiliary coordinates for each of e+1 gates. Original ground inputs are preserved through the actual embedding, with unused functional coordinates fixed to raw unit as before. e=0 and zero-valued inputs are included.

Full conjunction wiring, binary literal composition, actual successor equation insertion, raw numeric syntax encoding, encoded bit complexity, runtime, collision/aggregation and hardness are separate obligations. This is not variable exponentiation and not a claim of polynomial size in the binary length of e. No accepted definitions or manuscript are modified.
