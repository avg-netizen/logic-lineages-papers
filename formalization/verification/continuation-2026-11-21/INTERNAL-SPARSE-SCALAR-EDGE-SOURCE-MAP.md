# Paper 16: one selected physical packed scalar edge

## Original source, Settings and packed context

`16-persistent-marking-termination-ordering/sections/ordinals.tex`, lines
70–77, uses the original finite primary quotient; the edge here is the
original **elementary class exchange** used inside the least-code program.
It is not raw positive reduction, a raw rewrite certificate, or quotient
positive reachability.

`NumberedWindowScalarAlgorithm.Settings` retains all three original
components (window, allowed type list, equivalent-head pairs). Its `edge s g
ty w v` is the original `NumberedWindowExchangeAlgorithm.bits
s.equivalentHeads w v` term bit and **both** `admitted s g ty w` and `admitted
s g ty v`. Both use the same original g and requested ty. Admission is
original lexical typing conjoined with the original window bit; the
exchange term bit already contains raw term syntax at each endpoint before
the contextual exchange table row. No independent new endpoint-bit
semantics is substituted. The allowed type list remains part of the same
Settings for the subsequent cover, even though this edge does not read it
as a separate operand.

The physical context input is the original polynomial field code. Its
one actual `NumberedWindowFieldAlgorithm.unpack ctx : Option (List Nat)`
is either successful with that **one ordered list g**, including the
valid empty list, or absent. `packedEdge` is precisely the resulting
`Option.any` with the original edge at g. It never treats a malformed
code as the real empty context, never calls the older
`ScalarProgramProof.edgePrim` over `Encodable.decode … .getD []`, and never
folds over alternative contexts. `unpackPacked` gives the calibration at
each successful original `pack g`. The numerical conditional comparator
can split only on that same original unpack result to verify both guards
together.

## One actual AST and exact contracts

The executable `edge4 X W : Program 4` uses the current directed scan's
same physical `edgeTape ctx ty w v`. It uses original exact-one
`InternalAcceptance.conjunction` with:

- exchange X at projected slots 2,3, on exactly [w,v];
- original window/admission W at slots 0,1,2, on exactly [ctx,ty,w];
- **the same** W at slots 0,1,3, on exactly [ctx,ty,v].

`ActualTermExchange s X` is the exact all-Nat successful term bit of the
actual exchange algorithm at the fixed (s.equivalentHeads).
`ActualPackedWindow s W` is the unchanged original #711 callback contract
in `NumberedWindowInternalSparseTypedRawTargets`, using precisely
`(unpack ctx).any (fun g => admitted s g ty q)` on its physical tape.
`ExactPackedScalarEdgeCalibration` combines those named exact callback
premises only on the numerical side. It compares the same physical edge
to `packedEdge` for every raw Nat tuple, including malformed context,
same or distinct endpoints, and admitted/unadmitted endpoints.

`ExactSelectedPackedScalarEdge` chooses actual X and W at the same
original s, then retains that very `edge4 X W` with its calibration.
It does not choose an independent extensionally equal Program4. Planned
proof suppliers, not target imports: fix the actual head pairs of
`NumberedWindowExchangeProgramProof.bitsPrim`, uniquely take the Boolean
term coordinate, convert it to the numeric bit, and extract a real
arity-two program via `GorbowPRProgram.Proof.allPrimitiveFunctions`.
Original #533 `exact_ContextualExchangeProgram` already returns the encoded
pair of term/argument bits at [encoded head pairs,w,v], not a unit term bit;
no implicit equality to that whole pair program is assumed.
`NumberedWindowInternalSparseTypedRawPackedWindowProof.packedWindowWitness`
(#711) supplies the actual unchanged W with the exact packed context.
Neither choice proof is imported into this target-only Lean closure.

`ExactOpenPackedScalarEdge` is a literal original object-calculus
equivalence at arbitrary body, ordinary context, and arbitrary open
terms using the same physical X/W. One direction exposes their three
actual unit graphs at exactly those projected arguments, and the other
builds the original edge graph from those same calls. Exact-one graph
conjunction and composition intro/recover are legitimate existing
proof suppliers. This does not use numerical calibration as an
object-calculus premise or prove an internal exchange-table or
lexical/window graph meaning theorem.

## Later use and boundaries

When the selected E is used, it is the **same** `edge4 X W` passed to the
actual `scan E` and `pass E`; their current parameterized statements
remain unchanged. On actual successful unpack, directed numerical scan
and filter calibration can instantiate the original `ClassAlgorithm.advance
(edge s g ty)` without any changed list order, duplicates, or endpoint
orientation. In a malformed context this E rejects, but an equality
stutter in the scan can still pass independently of E; an enclosing
selected least checker must still use actual context rejection.

For the original typed manuscript instance, #536 connects fixed
`Settings` and actual encoded Gamma/type to genuine finite guarded
exchange, and the existing original term codec and
`PrimaryExchangeChecks.exact_FiniteExchangeReflection` identify that
numeric bit with the original `WindowExchange`. #687 gives literal
same-vertices-list preservation for original guard-success edges.
These are external numerical/Lean meaning suppliers, not ordinary open
graph reflection. An ordinary structural exchange witness, open
head/permutation interpretation, output carrier, raw matching,
installation of a different application program, complete rounds,
complete least and numbered accessibility all remain out of scope.
