# Raw source-DAG operations supporting comparator

Source compiler.tex computable construction uses actual finite shared source DAGs. This packet is supporting infrastructure only, not a numbered compiler claim.

Actual suppliers are GroundEquivalence.DAG/Ref/DAG.insert and ScopedDAG.Ref.front/back, prefixRename, append, rename/renameInput. The accepted exact RawSourceDAG codec is used without changing its six frozen files.

Five endpoints:
1. References: literal index preservation/shift for front/back/insertSpec, exact local-prefix renaming and inserted-ground variable indices.
2. Append: exact encoded graph identity and literal length sum.
3. Rename: actual typed renaming table length, encoded graph identity, exact packed Input code identity (including target context and unchanged root/type), and literal table length. Renamings need not be injective; no vertex merging/deduplication occurs.
4. Insert: exact graph code identity against genuine DAG.insert and table length. Insertion changes root specs from [] to [ground]; it is not represented as a valid closed-prefix Input by itself. Later eraser introduces the lambda to close that prefix.
5. Primitive: actual structural raw routines are primitive recursive on every raw input. These are total, unchecked helpers, not claims that arbitrary malformed data is well typed. Rename preserves malformed/non-variable payloads; insert appends ground to every prefix and only shifts a well-shaped variable payload. Out-of-domain renaming lookup uses default zero. Exact typed identities ensure defaults are never needed on compatible typed inputs; checked external wrappers remain separate.

All seven constructors, all original vertices, repeated/unused references and lexical prefixes are retained. No expanded-tree equality substitutes for exact graph equality. No assumed validity oracle, global compiler correctness, all-gate serialization, or polynomial bit/runtime credit is supplied by this packet. Subsequent checked application/eraser/aggregate and whole input/compiler codes remain unpaid.
