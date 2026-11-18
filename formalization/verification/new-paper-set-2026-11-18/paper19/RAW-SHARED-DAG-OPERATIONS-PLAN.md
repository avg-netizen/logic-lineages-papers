# Actual raw shared-DAG operations: next staged plan

## Source and accepted boundary

RawSourceDAG supplies a checked exact dependent codec for the actual GroundEquivalence.DAG/Input, with a concrete primitive validator and total reifier. CompilerComposition already proves actual source-table bounds and generic semantic comparison, but does not establish joint syntactic computation. The next steps operate on literal typed DAG encodings, not expanded terms.

Read current actual definitions: WWScopedSourceDAGDefinitions (append, prefixRename, rename, application, eraser, aggregate), SourceGroundEquivalenceDefinitions (insertSpec/DAG.insert, all seven constructors, upper/lowerInput), SourceBooleanCompilerDefinitions (all five Program constructors and lower). The compiled Boolean arithmetic gate layer includes real sort; no legacy inert-tag transfer is proposed.

## First small packet: literal graph transformations

1. Append: encodeGraph (ScopedDAG.append a b) = encodeGraph b ++ encodeGraph a. Prove Ref.front preserves the index and Ref.back shifts it by the exact length of the front. These are literal graph/root facts; no semantic quotient.
2. Free-context renaming: represent an actual typed renaming Γ→Θ by the finite index list of all Γ variables in order. For a variable node with local prefix length k, leave i<k unchanged and map i≥k to k+rho[i-k]. All other node payload references and all local prefixes are unchanged. Prove the raw transformed graph equals encodeGraph of actual ScopedDAG.rename for every typed renaming, and root index is unchanged. List indexing is total with a documented default outside valid renaming inputs; typed correspondence ensures those defaults are never used. Later checked external wrappers must validate context length and target types before applying the routine.
3. Insertion: append code 0 (ground) to each local prefix; for variable payload i leave i<old-prefix-length unchanged and increment i≥old-prefix-length. Preserve every other payload reference. Prove exact equality with actual DAG.insert and index preservation under Ref.map insertSpec.
4. Prove actual raw routines primitive recursive and exact table lengths: append sums; rename/insert preserve lengths. All seven node constructors and unused/repeated vertices retained. Helpers are total raw routines; arbitrary malformed node payloads receive an explicit deterministic structural behavior, not a claim of successful typed decoding.

These foundations need no generic typed decoder oracle or whole compiler recursion. Freeze exact targets only after conceptual approval. Native stages may separate structural graph identities and primitive routines.

## Following checked composition packet

Use existing valid plus explicit compatible context/type tests to implement raw variable/zero/successor, application, eraser, detectorLeft/Right, aggregate, and upper/lower wrappers. Every external checked operation returns none for rejected inputs. Return some exact encode of the actual typed operation on valid compatible inputs; derive actual decode/reconstruction using the accepted codec. For application, the first input root shifts by the second table length; for eraser, insert the first table, append the second, add literal lambda/application nodes, and account for the extra root shift. Aggregate preserves the actual right fold and zero-pair convention, including empty input. Prove concrete computation and literal counts rather than only denotation or output existence.

## Whole compiler stages still owed

Actual raw typed arithmetic ports/all four gates including sort; Boolean DAG validation and shared root/port decoding; five-constructor Program code with arbitrary encoded source tables; concrete lower/Plan construction, same nine witnesses and ten equations; compiled forest/aggregate/wrapper reconstruction; total malformed input behavior and joint Computable composition. Explicit source input/AST or shared-DAG normalization codes must be linked, not merely accept assumed already-normalized data. Existing polynomial actual table bounds transport only after exact reconstruction. No stronger polynomial serialized-bit runtime claim is added.
