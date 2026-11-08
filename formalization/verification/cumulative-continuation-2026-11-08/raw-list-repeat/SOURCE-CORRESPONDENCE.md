# Internal repetition over the original raw-list code

This supporting component is a prerequisite for the concrete original
application-step preservation argument toward paper 06, `lem:id1`. It does
not prove application-step acceptance, certificate lifting, normalization,
or the paper's all-term endpoint. No numbered source statement is promoted.

## Exact program and argument order

`InternalRawListRepeat.repeatProgram transition` is literally

    InternalRawListRecursion.listRec (.projection 0)
      (.composition transition (fun _ => .projection 1))

for an arbitrary `transition : Program 1`. The program has arity two and
receives `[raw list code, initial state]`. The inherited list-recursion step
has arity three and receives `[head, recursively computed tail result,
initial state]`, so projection 1 applies the transition to the recursive
result. The head is ignored. The nil/base program returns the initial state.

The list constructor remains `InternalListCodec.consCode`: the original
successor-of-pair code. No decoder, encoder, parser, graph compiler, source
term, numeric fuel, rank, fixed-point operation or ambient calculus changes.
The repeat implementation uses the existing raw-list recursion table; that
table is not an extra premise of any target.

## Frozen original-calculus statements

All three targets quantify arbitrary `Positive (Fin 1)` bodies, original
unary PR ASTs, variable types and symbolic arithmetic terms. `Graph` below
means the literal `InternalControlGraph.programGraph`, and proofs must be
`InternalCalculus.Derivation body []` in the unchanged original calculus.

1. `Graph(repeat transition, out, [0, initial])` iff `out = initial`.
2. Given `Graph(consCode, code, [head, tail])` and
   `Graph(repeat transition, tailResult, [tail, initial])`,
   `Graph(repeat transition, out, [code, initial])` iff
   `Graph(transition, out, [tailResult])`.
3. Given `Graph(consCode, code, [head, tail])` and
   `Graph(transition, next, [initial])`,
   `Graph(repeat transition, out, [code, initial])` iff
   `Graph(repeat transition, out, [tail, next])`.

The third law is the front-cons identity required to consume a source path
cell while updating an accumulating application state. In particular, it
has no assumption that a standard-model evaluation succeeded, a decoded
list is canonical, a source checker accepts the head, or a numeric bound
holds. Those are separate obligations for an eventual application consumer.

## Checked internal argument, not an additional assumption

The ordinary law follows from the already checked original raw-list
recursion cons law and original graph composition/functionality. The
front-cons law uses genuine internal list-code induction. The checked
full-language invariant universally quantifies the initial state, its
transition result, a repeat result, and the transition of that result. It
states that the latter is the repeat result at the transitioned initial
state. Nil follows by graph equality; cons follows by the original ordinary
unfolding and the tail induction hypothesis. Original totality and
functionality then obtain both directions at the same arbitrary output.

No semantic truth-to-derivability rule is permitted. Full-language
`InternalListInductionProof.actualOriginalListInductionAtCode` is the
inherited proof rule available for the induction. The original graph
compiler's totality, uniqueness and equality-transport APIs provide witness
management in arbitrary contexts. Any external evaluation calibration would
be separate and is not part of this three-target packet.

## Validation boundary

The definitions, targets and preflight were frozen and the exact preflight
passed before proof authorship. The final exact gate passed all three
aliases and their actual axiom-closure audits, with only `propext`,
`Classical.choice` and `Quot.sound`. All 1,047 local modules in the focused
proof closure match successful native receipts for their current source
bytes. The original frozen hashes remain unchanged.

Three failed candidates are retained locally. Repairs added two missing
namespace opens and explicitly unfolded a local formula abbreviation for
rewriting. The commutation induction and all three frozen statements were
unchanged. Candidate 004 passed. See `ACCEPTANCE.json` and `SOURCE-PINS.json`.

This component checkpoint does not include shared integration or publication.
No full-root or remote-CI build is claimed. Existing frozen files and all
checker, dependency, resource and axiom policies remain unchanged.
