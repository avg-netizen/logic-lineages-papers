# Canonical supported Plan spine: numeric compilation interface

This is an implementation bridge for the literal source conjunction construction, not a numbered source theorem. Paper09 hardness.tex lines 294–314 give the arithmetic conjunction and restricted source construction; this component preserves the already accepted Plan.compile forest exactly. It does not establish complexity or a code-producing map from the halting index.

The fixed representation is List (Nat × (Nat × (Nat × Nat))). Its right fold is appropriate because Plan has one recursive continuation. Tags 0,1,2,3,4 denote a source equation, equality gate, addition gate, one gate, and existential coordinate respectively. Sort is encoded by reserved tag 5, interpreted inertly on raw data, and excluded by Supported from every typed calibration. Every other raw tag is also inert. Equation payloads are the exact existing encodeTerm values of actual DAG leaf terms; this is deliberately not a sharing-preserving DAG serialization.

ExactCompilation: supported spine instructions have tags at most 4; run returns exactly Plan.witnesses and the ordered encodeTerm pairs of the existing compile result. At an equation the accumulated tail witness count shifts both source codes with binder-aware sourceCode. At a gate, ports are first shifted by the tail witness count, while eqForest/addForest/oneForest allocate their additional nine wires. Old tail equations are shifted by nine, and generated equations precede them. At existsGround the count increases by one while the already compiled body forest stays unchanged. Zero port 0 stays literal zero. No arbitrary renaming is represented.

ExactAggregate: the existing source aggregate of that exact compiled forest has precisely aggregateCode's two output codes, preserving orientation. No semantic or hardness conclusion is bundled.

UniformPrimitiveRecursive: the instruction transition, list right fold, and final aggregate are primitive recursive on all raw lists/products, using their standard Primcodable representations. Prerequisites are the accepted prefix pair/list shifts, primitive forest builders, list append and primitive recursion through list_foldr. There is no unbounded recursion, parser, typedness claim for malformed data, scalar Nat wrapper, effective (b,e)-to-spine construction, source bit-size bound, or runtime claim.

All existing accepted sources, semantics and frozen packages remain unchanged. Verification only; no export or publication.
