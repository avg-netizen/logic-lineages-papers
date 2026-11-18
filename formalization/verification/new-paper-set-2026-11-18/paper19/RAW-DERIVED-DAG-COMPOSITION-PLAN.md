# Derived checked detector, aggregate and literal wrapper plan

## Accepted suppliers and next scope

Use exact RawSourceDAG codec, primitive append/insert/rename graph operations, and accepted checked application/eraser. The next supporting packet constructs actual detectorLeft/Right, aggregate and lower/upperInput graph codes, validates all external raw input and proves exact output reconstruction. It does not advance the numbered compiler on semantics alone.

## Concrete constructors and checked boundary

Define pure raw detectorLeft/Right by the literal nested eraserRaw calls matching ScopedDAG definitions. Define raw aggregate on a declared raw context Γ and list of pairs using the same right fold: empty returns two literal zero inputs (table one zero node, root0, ground); each nonempty step applies raw eraser to detectorLeft/Right and the corresponding prior fold output. Every supplied pair is retained in the actual tables with precisely the duplication already present in ScopedDAG.detector/aggregate, not erased/deduplicated as a semantic optimization.

External detector guards require both inputs valid, same context and ground outputs. External aggregate guard requires every component valid, ground and exactly the declared context. Empty input is accepted for every declared type-code context (all Nat type codes decode); no accidental requirement of a nonempty list. Checked return is Option(Code×Code), none iff that concrete guard fails. Implement guard via finite list fold, not classical forall oracle.

For wrappers, implement literal magnifyRaw, identityRaw and constantRaw constructors following actual GroundEquivalence definitions; lowerRaw/upperRaw compose them. MagnifyRaw table is app(root refs1,0) :: zero :: lambda(body old root) :: inserted original table. Identity/constant table is app(refs0,2+old root) :: lambda(ref0) :: var-at-local-ground-prefix/zero-at-local-ground-prefix :: original table. Output context unchanged, root0, ground. Thus lower/upper add six nodes exactly; do not use eraser(input,zero) as a literal surrogate. External wrappers require valid ground input and reject malformed/nonground input.

## Exact proof obligations before freeze

1. Literal typed encoding identities for both detectors, pair aggregate on every typed list, and both actual lower/upperInput wrappers; all root indices/prefixes/table vertices preserved.
2. Arbitrary raw successful calls reconstruct compatible typed input witnesses (for aggregate, one same-context typed list whose component encodings are exactly the supplied raw list), and outputs are exact encodings of the actual operations with successful actual decode. Computation is the concrete raw functions; witnesses are only soundness conclusions.
3. Rejection iff concrete guard false, all successful output validity/context/root/type, and exact counts. Each detector has 2*(na+nb)+6 nodes; each aggregate side has sum over pairs of (2*(na+nb)+8)+1; each lower/upper wrapper has n+6. Empty aggregate count1 per side, not an assertion that its actual scalar equals zero.
4. Joint Computable checked routines on all raw inputs. Raw detector/wrapper constructors are primitive recursive from previous raw eraser/insert operations; raw aggregate and guard are finite primitive/list folds. Transport accepted actual validator computation; no search for typed witnesses is used to implement results.

Suggested staging: first literal wrapper/detector typed identities and raw computation; then list aggregate same-context reconstruction and counts; then full checked packet union. Concrete freeze may separate these to keep native proofs bounded. No native without scope review and parent ticket.

## Remaining whole compiler route

Checked variable/zero/successor and noninjective typed renaming tables, real four arithmetic gates including sort, actual Boolean DAG/root validation, five-constructor Program codes, normalization/input coverage and exact Plan/forest construction. Only after joint typed reconstruction and Computable composition can existing polynomial actual source-table bounds yield the complete numbered compiler. No claim of polynomial serialized-bit time is added.
