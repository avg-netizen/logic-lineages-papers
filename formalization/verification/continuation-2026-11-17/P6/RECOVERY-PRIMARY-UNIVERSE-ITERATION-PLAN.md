# Next original primary-universe closure step

Read-only source plan, 2026-11-17. This is not a frozen comparator, proof or acceptance record. The installed edge endpoint and its recursive prerequisite must first pass native verification and review.

## Exact proposed next caller

Fix n/arity, H = OriginalConcreteHeadSignature.signature n arity,
G = OriginalDecodedContextValidity.contextGuard n,
T = OriginalTypedDecoder.target H G,
Q = OriginalCandidates.candidates n arity H,
P = SeededPrimaryPool.pool T Q,
E = OriginalConcreteStructuralEdge.edge n arity,
L = SeededPrimaryPool.primary T Q E,
M = OriginalUniverseDomainCoverage.member n, and
W = OriginalGuardedHeadSourceCoverage.window n arity.
Keep this one literal tuple throughout.

Proposed endpoint: arbitrary symbolic seed, parameter, output and candidate;
observed seed=(seedType,seedRaw), candidate=(targetType,targetRaw), and
parameter=(context,gamma); original T(seed,parameter)=1; actual L output;
actual contains(output,candidate)=1; original universe Accepted H M W false
seedType seedRaw gamma context. Conclude the same universe Accepted at the
observed candidate type/raw and the same gamma/context. Do not assume candidate
universe success, candidate Code, target typing, an arbitrary edge supplier,
external decoded reachability, pool adequacy or count closure.

Seed admission is explicit in this endpoint, as in the installed-edge theorem.
Removing it would require a separately checked original universe-to-target
admission bridge. The candidate type is observed, not assumed equal to seedType.
If later consumers need equality, accumulate it separately from the installed
edge's exact type-preservation clause.

## Sound internal induction route

1. Define a formula U(reached) in the original calculus: universally quantify
   candidate, typ and raw; contains(reached,candidate)=1 together with the actual
   pairing graph candidate=(typ,raw) implies Accepted H M W false typ raw gamma
   context. Carry the fixed seed/parameter/pool graphs and seed admission in
   the induction environment. This internal universal is needed because the
   successor branch exposes an existential source; an external pointwise
   hypothesis at one fixed vertex is insufficient.
2. Prove U(singleton seed) from the seed universe premise. Existing
   PrimaryCarrierBound.RunProof.singletonMember derives candidate=seed from
   actual singleton graph + membership. Use pairing functionality/injectivity
   and congruence to transport seed acceptance to the independently observed
   candidate fields. No syntactic equality of separately queried fields.
3. Prove expansion preserves U. Use
   PrimaryExpansionSoundness.Proof.expansionSoundness (or the forward direction
   of expansionCharacterization). Its literal old-member branch uses U(old).
   Its new-member branch supplies actual pool membership and sourceWitness E
   old candidate parameter. Eliminate the latter using
   PrimaryExpansionSoundness.WitnessProof.casesWitness, retaining the same
   parameter and pool under its binder map. Query that source's actual pair
   fields (using existing pairing projection/totality lemmas), specialize U(old),
   and invoke OriginalInstalledFilteredEdgeUniverse.Proof.atSource with the
   actual edge and new candidate's actual pool membership. This is precisely
   where source universe acceptance is derived from IH, not postulated.
4. Lift step 3 to arbitrary symbolic count by the original object-arithmetic
   natInduction for PrimaryIteration.iterate E. Use PrimaryCarrierBound's
   InductionDefinitions/InductionSyntaxProof/InductionProof as the concrete
   template: zeroValue, successorRecover, graph functionality, capture-free
   substitution/renaming, and AtCount universally quantified over runtime out.
   The invariant can imply U(out) from U(initial), avoiding expansion of every
   packed-field variable into the recurrence matrix.
5. Recover run E from its literal singleton composition, as in
   PrimaryCarrierBound.RunProof.runCarrier. Then recover L's admitted branch
   and its actual count/pool outputs exactly as
   SeededPrimaryPool.InternalProof.internalPrimaryCarrier does. The count is
   length(P), but induction works for every symbolic count, so no cutoff
   correctness or finite graph saturation theorem is needed for preservation.
   All queried count/pool/singleton witnesses are eliminated internally.
6. Instantiate U(output) using the exact observed candidate pair and actual
   output membership. Freeze the literal endpoint and comparator expansion
   before implementing its proof. Review binding helpers and full source pins;
   native endpoint + recursive evidence remains mandatory.

## Existing helpers and exclusions

PrimaryExpansionSoundness.sourceWitness is an actual existential packed source
with old-list membership AND E(source,candidate,parameter)=1, not a semantic
promise. Its WitnessProof supplies witnessRename/witnessSubst/casesWitness.
PrimaryIteration.run keeps original singleton, order, duplicates, and fixed
pool/parameter. SeededPrimaryPool.primary is LengthAlignedPrimary.primary with
this exact pool; do not replace it by an arbitrary generic calibrated program.

The already checked primary-carrier inclusion alone is not universe closure:
its destination pool has merely PLAIN filtered typing, which is weaker than
universe acceptance. Similarly, the standalone one-edge endpoint does not prove
that all reached sources satisfy its universe premise. The induction above is
necessary and must not be replaced by an assumed all-reached invariant.

## Residual original-paper gap

This yields an internal source-universe preservation supplier for the actual
primary list. It does not establish global accessibility or promote a numbered
statement. TARGETS.json still lists Paper 6 lem:structural, thm:stable,
lem:id1, thm:upper, lem:realclosure, thm:iteration, lem:primitives and thm:height
pending. In particular lem:id1 still requires the complete same-tuple original
computability/accessibility consumers, including neutral application-spine,
lambda/substitution, multiset/numbered constructor and closed all-term coverage.
No new interpretation stability, BH bound, realization or iteration result
follows merely from this carrier law. Reconcile the actual consumer signatures
before choosing the next promotion target.
