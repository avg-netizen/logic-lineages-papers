# Direct L decomposition: literal reached-list expansion

Design only; no definitions/targets/proofs authored for this successor.

## Original source route (unchanged)

ContextUniformPrimary.classCodes enumerates actual size/label bounds from q,
actual sourceHeads, Gamma.length and twice the code-size bound. candidates
filters that ordered list through rawStructuralDecode. vertices is literally
q :: candidates, including repeats. step is literally

  reached ++ pool.filter (fun r => reached.any (fun a => packedCodeExchange ... a r))

reachable iterates this step from [q]; primaryList uses vertices.length as its
cutoff, NOT a deduplicated cardinality. Membership.entriesCode maps the actual
RawPacked entries through their existing encoding into numbersNumber. The
transparent D result shows this encoding is the original packedNumber.

## Next concrete AST layer

Expose the actual two right folds rather than choosing an opaque step Program.
Keep an edge Program E with inputs [source,candidate,parameter]. Its separately
selected native leaf must compute original packedCodeExchange after the original
context/Object/rawPacked decoders, including failed decodes returning zero.
No internal edge correctness is assumed from that native calibration.

1. anyEdge E: listRec zero step over reached, parameters [candidate,parameter].
   Step inputs [head,tailResult,candidate,parameter]. Normalize the actual E
   output to exact-one; return one on acceptance, otherwise retain tailResult.
2. filterReached E: listRec zero step over pool, parameters [reached,parameter].
   Step inputs [candidate,tailResult,reached,parameter]. Test anyEdge E on the
   SAME original reached list (not the growing output). On exact-one acceptance
   cons candidate to tailResult; otherwise retain tailResult.
3. expand E [pool,reached,parameter]: use the existing unchanged
   InternalApplicationValidityStackAppend.append to append reached followed by
   filterReached output. Do not reverse, deduplicate, sort, or omit annotations.
4. iterate E: literal primitive recursion from singleton seed; retain fixed
   pool and parameter on every iteration. Supply the actual encoded pool length
   as cutoff; raw code itself is not the vertex count.

The encoded native calibration of this layer can be generic in E (in terms of
actual evaluate E), with a second source-correspondence theorem instantiating
the real original exchange leaf. Generic calibration alone is not completion.

## Independent internal laws worth proving first

Exact nil/cons rules for anyEdge and filterReached, using actual E acceptance
or rejection and actual consCode graphs. Then an arbitrary runtime invariant:
actual membership in reached survives actual expand output, independent of E.
This follows from literal append and membership recursion; it neither assumes
nor proves exchange semantics. A later original arithmetic induction lifts
preservation to every count of the actual iterate.

Next pay actual edge-hit introduction into filtered pool, retaining both the
actual pool occurrence and reached occurrence and E graph. These precise laws
are useful for internal reachability and must not be replaced by a semantic
Premise field.

## Remaining opaque inputs and caveats

The ordered pool enumeration and original exchange leaf still need transparent
implementations/internal constructor laws. Initial native selection of those
Programs may supply calibration ONLY. Their graph correctness cannot be
inferred by evaluation reflection. This decomposition exposes genuine finite
reachability infrastructure without pretending those harder suppliers paid.

Source primary relation/stable-pair/transitivity issues previously documented
remain unchanged. In particular no unrestricted equality of primaryList rows,
E-to-primary compatibility, root-signature completeness, cancellation, I/C or
accessibility is claimed. Every successor retains the source's literal list
order, duplicate behavior, finite cutoff and typed packed validity.
