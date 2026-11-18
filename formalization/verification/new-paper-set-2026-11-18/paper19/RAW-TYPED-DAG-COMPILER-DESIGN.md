# Concrete raw typed/shared-DAG compiler design

## Inspected gap and smallest first packet
GroundEquivalence.DAG has exactly seven actual primitive constructors: var, app, lam, zero, succ, case, recursor. Each vertex carries a local binder prefix Delta and result type; references point into the preceding typed spec list. Input has one root reference of spec ([],tau). No existing DAG code codec was found in the current source-name search. SourcePlanSpineCode cannot replace it: sort is unsupported tag5 and leaf payloads are unfolded terms.

First supporting packet should therefore be a concrete raw source-DAG codec, not the entire compiler. It must preserve ALL seven constructors and all edges, including repeated references, arbitrary internal types and supplied recursors. No restriction to arithmetic source fragments.

## Raw finite data, no semantic oracle
Use inductive RawTy = ground | arrow RawTy RawTy, a syntactic List encoding (then canonical Encodable Nat encoding). RawSpec = List RawTy × RawTy. RawNode stores tag, declared RawSpec and finite Nat payload fields. A RawInput contains free context List RawTy, oldest-first List RawNode, root Nat and declared output RawTy. Reference indices count backwards in the current newest-first typed spec list, matching Ref.here=0/there=+1. Variable indices similarly count in Delta++Gamma. The local prefix and types are encoded explicitly rather than reconstructed by source denotation.

Node interpretation/validation:
- var: look up variable index in Delta++Gamma; require exact declared result type.
- app: lookup TWO earlier refs with same Delta, types sigma→tau and sigma; result tau. No new/unfolded subtrees.
- lam: one earlier ref with local prefix sigma::Delta and result tau; output arrow sigma tau.
- zero/succ: require fixed result ground/ground→ground.
- case/recursor: carry explicit parameter type and verify exact caseType/recType.
Reject unknown tags, missing/extra payloads, invalid/dependent spec mismatches and out-of-range references. Final root must look up ([],declared output). Checks are structural finite list/type operations, with decidable syntactic equality, not ordinal or program evaluation.

Typed encoder emits exactly one RawNode for each DAG constructor, preserves the actual list of specs and root index, and records every variable/ref index literally. Typed decoder returns Option of the dependent packed actual Input; failed checks yield none. On encoded typed input, decoded specs/graph/root equal the original Input (or explicit HEq after unpacking indices), not merely equality of expanded Input.term. Prove encode(decode code)=canonical code for validated normalized nodes if needed; the required primary direction is decode(encode d)=some d plus actual node-count equality. This establishes all supplied source tables retain sharing.

To avoid hiding effectivity in the dependent decoder, first define raw validation and indexed construction routines by finite recursion and give a total raw normalization/roundtrip function. Prove Computable of the raw functions using concrete Encodable instances, then connect their outputs to the typed reconstruction. Classical choice is not an implementation of decoding. Invalid raw inputs have an explicit fixed result (none for validation/decoding; final compiler eventually emits two fixed zero DAGs in empty context). Success or failure is computed on every raw code.

## Subsequent executable operations, separate exact packets
1. Primitive raw DAG transformations: append (adjust back references), free-context rename (finite typed index map), insertGround (local-prefix insertion/variable remap), application, eraser, I/K wrappers, aggregate. Prove exact typed encode commutation and Computable jointly for every input; operations must preserve every constructor including case/recursor. Actual table counts are the checked typed ones through exact reconstruction.
2. All-gate raw Plan forest: use new distinct five-payload instruction representation (tag plus four ports), with genuine sort carrying a,b,l,h. Equation payloads are RawInput tables, not unfolded term codes. Validate input reference indices. Define reverse fold mirroring compile, rename/shift whole forests using operation1, implement every gate's real nine-witness/ten-equation forest. Prove encoding of compile exactly equals raw run. Do not edit legacy tag semantics or inherit Supported restriction.
3. Raw interleaved formula: finite tagged natural/Boolean instructions with earlier typed natural/Boolean indices, source RawInput payloads, binary constants as Nat, and final root. Validate sequential context growth. Implement two-slot normalization and Boolean flatten plus literal binary spine; compare with the actual typed normalize/lower outputs. The language includes all eq/le/lt/neg/conj/disj/add/literal/observation/unary constructors. A malformed code gets the fixed output; every valid typed input is accepted.
4. Compose the total raw compiler, output both typed source DAG tables and shared free-context size. Prove Computable jointly in the finite input code and exact reconstruction of the literal typed comparisons. Syntax compilation is independent of p/f evaluation. The semantic and actual polynomial DAG bounds then follow from CompilerComposition. No polynomial code-bit runtime/size theorem is required.

## Exact first proposed scope boundary
Freeze only after review: (i) all-type/variable/reference codec lookup correctness, (ii) all-seven-node typed encoder→decoder reconstruction, (iii) exact source table length and root/reference preservation, (iv) genuine total Computable validator/raw decoder representation. If the dependent decoder is difficult to expose directly as a standard Encodable function, choose an explicit raw canonicalization output plus a proved deterministic typed reification relation with UNIQUE output and total effective construction, never an existential arbitrary reifier. No numeric-only/expanded-tree stand-in.

This is a substantial new representation foundation, not a trivial reuse of old PR tree codes. Full compiler remains pending until all subsequent all-gate and whole-input operations are reconstructed and computability proved. Native only under fresh reviewed target/proof tickets and unchanged caps.
