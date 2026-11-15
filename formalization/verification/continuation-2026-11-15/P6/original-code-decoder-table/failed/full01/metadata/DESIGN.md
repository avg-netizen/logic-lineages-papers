# Original bounded code-decoder table: exact3 freeze

## Source correspondence and inventory
Original NumberedCodeParserTable.codeTable n bound 0 is replicate(bound+1)false. Its successor is List.range(bound+1).map(codeNext n previous). NativeRows and NativeTable retain this exact ascending order, width, zero cell and Bool interpretation. New explicit AST uses original primitive recursion, numeric cons/append and checked OriginalCodeDecoderStep.step. No selected opaque supplier is introduced.

Duplicate inventory found OriginalHereditaryDeletionRows.scan, an ascending append-singleton scanner with paid actual length/lookup infrastructure. That scanner hardwires erasure observation Q to erasedPacked/erasedParameter, so it is not an arbitrary-index codeNext map and is not silently reinterpreted. Reuse its original append-singleton length and OriginalInternalAppendLookup/OriginalContextInsertion below infrastructure; a distinct direct row AST is required. No existing pure numeric range/zeros Program or direct codeTable AST was found by definition search.

## Exact AST
zeros(count) is primitive recursion from empty numeric list, prepending zero per step. seed(bound)=zeros(bound+1). nextRow(bound,previous) starts with singleton step(previous,0), then appends singleton step(previous,index+1) at each successor. TableProgram(fuel,bound) starts at seed and iterates nextRow(bound,previous). Thus append retains original ascending index order instead of reversed caches or shifted indices.

## Internal target and proof duties
InternalRowLookup is all-raw and uses only actual nextRow graph, original object-language strictLess(index,suc bound) (equivalent to index≤bound), and actual original lookup graph. It assumes neither a native image, Boolean table, row length, sortedness, node validity, nor a lookup-at-correct-index premise. Prove actual row length internally and simultaneous lookup correctness by original induction; split old-prefix vs final index using actual bounds, append lookup and singleton facts. All recursive-row/step/singleton/output witnesses are internally supplied. This native table plus internal row is partial progress toward the internal recursive guard, not that guard itself.

## Remaining limitations
Internal table-iteration validity invariant, sufficient-fuel correspondence and actual recursive code-guard equations remain open, as do decodeCode's filter integration at concrete runtime, encoded-node conversion, invalid/default[] dependency supplier calibration and installation. No whole E/accessibility/source-computability completion claim. OriginalCodeDecoderStep FULL02 passed native exact2 receipt1794746394600458384-6; independent evidence acceptance was pending when frozen. No proof authored before independent review/preflight; coordinator owns compiler/publication.
