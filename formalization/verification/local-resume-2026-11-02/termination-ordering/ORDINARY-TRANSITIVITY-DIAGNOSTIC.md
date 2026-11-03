# Checked ordinary-domain transitivity obstruction

The immutable local original calculus is **not transitive even on three actual
ordinary Source.Term embeddings**. Its Weak-then-Strict compatibility target
is false as well. This is an exact Lean result about the specified local
rules; it does not establish that Kop's published theorem is false.

## Exact checked scope

Use ranked heads Z<H<K<F of arities 0,0,1,2. Let k=K(H), and put

```
P = (lambda x.F(x,Z)) k
T = F(k,Z)
U = F(H,H).
```

All three are closed, ground-typed, literal ordinary source terms. Their
concrete symbol names are 0,1,2,3; no other symbol occurs in them. Let q be
the literal marked application whose base is [(lambda x.F(x,Z)), k], and let
s=F(q,Z).

The four frozen aliases prove:

1. ORIGINAL P Weak T and ORIGINAL T Strict U.
2. No ORIGINAL P Weak U.
3. Not OrdinaryTransitivityTargets.ActualOriginalTransitivity.
4. Not OrdinaryTransitivityTargets.ActualWeakStrictCompatibility.

Receipt1793669543703102170-2, gate-local returncode0, full axiom closures only
propext and Quot.sound. The two comparator files compiled and froze BEFORE
proof authoring in1793668416282449179-2. The full proof's actual compiler
diagnostics were repaired without changing either frozen comparator.

## Why the two steps hold

The marked application q selects k with the empty tuple. Hence q Weak k.
Selecting the lambda from q with the single whole-source argument returns
s=F(q,Z); Fun then gives s Weak T. Put and Select give P Weak T.

k Strict H follows by marking K(H) and selecting H. For T Strict U, mark
F(k,Z), remove its entire two-element base multiset, and insert H,H, both
strictly dominated by k. The marked whole source also weakly dominates H by
selecting k. This is a literal instance of the ORIGINAL Stat rule, not an
auxiliary In step.

## Why the composite has no finite derivation

The proof first pays the actual scalar exclusions Z notWeak H, Z notStrict H,
k notWeak U, and q notStrict H. The last is definitional: strictMark q=none
for the already-marked application.

A Fun proof from s to U would weakly match the Z occurrence to H, impossible.
A Stat proof from markedS to U has no removed source occurrence strictly
dominating H: neither q nor Z does. Thus no inserted occurrence is possible;
the equal two-element source/target lengths and a nonempty removed part
then contradict the required retained matching. Copy F to F is also blocked.

All remaining possible derivations lie in the cycle

```
q -> s -> markedS -> q,       P -> q.
```

Selecting k or Z instead terminates in the independent scalar exclusions.
The native application head cannot Copy to the higher ranked F. A genuine
simultaneous induction on n proves that NONE of q,s,markedS,P has an
ORIGINAL budget-n proof to U. Up padding is explicitly handled. The proved
five-way original/budget equivalence therefore excludes EVERY finite original
derivation. No timeout, maximum search depth, numerical test or termination
or transitivity assumption is used.

## Consequences and limits

The existing stronger arbitrary-marked auxiliary diagnostic remains valid,
but restricting endpoints to ordinary syntax does NOT repair the present
problem. The new counterexample uses the actual ordinary endpoint domain.

No unchanged comparison relation agreeing with these ordinary answers can be
made transitive merely by adding a missing proof: any transitive extension
retaining the two positive weak steps must change the negative P,U answer.
Likewise the current Weak-then-Strict compatibility implication is false.
This is a mathematical obstruction, not a Lean elaboration problem.

Do not silently alter strictMark, add transitive closure, weaken the frozen
target or promote a helper to a source theorem. A source-faithfulness repair
must explicitly determine the intended repeated-marking/Stat convention,
then prove the required correspondence and re-establish any changed decision
semantics. Idempotent marking is a possible convention to investigate, not
a proved unique repair or a source-fidelity conclusion.

The existing checked adequacy, literal decision and ranked-RPO statements
remain theorems of their exact frozen types. This diagnostic adds ZERO
numbered completions and does not change accepted source bytes. Full stable
pair, general WF, ID1 and ordinal obligations remain unpaid. No refutation
of well-foundedness or of the ranked restriction is asserted. Main alone
owns manuscript/source adoption and the global register.

## Portable evidence

- OrdinaryBetaTransitivityDiagnostic-ACCEPTED.json: exact declarations, frozen
  target types, current source/proof hashes, concrete receipt and gate log.
- OrdinaryBetaTransitivityDiagnostic-FREEZE.json: preproof comparator pins.
- ACCEPTED.json:34 bundles/85 fixed aliases, including TWO diagnostic bundles.
- OriginalCompositionFramesProof is checked conditional infrastructure only;
  its body-postcomposition premise was never promoted to full transitivity.

Primary reinspection (not a proof supplier for this finite diagnostic): Kop,
Higher Order Termination, author-hosted corrected thesis, chapter5 Definition
5.19, Lemmas5.24-5.30 and Theorem5.31,
https://www.cs.ru.nl/~cynthiakop/phdthesis.pdf. No published theorem is negated
without a separately established full source-convention correspondence.

## Follow-up consequence checkpoint

The SAME-witness consequences passed FIRST TRY at1793670058887479841-2
with only the standard three axioms. It additionally checks actual source
type-support confinement, BOTH positive Strict steps and NO Strict composite,
the remaining Strict-then-Weak compatibility refutation, and refutation of the
older raw-original-endpoint proposition. This adds zero numbered completions.
OrdinaryBetaDiagnosticConsequences-ACCEPTED.json owns the exact four types.

Finite-signature qualification is being paid explicitly in a separate Fin4
re-encoding; it is NOT yet accepted or inferred from this Nat-name encoding.

## Finite-signature guard: now checked

FiniteOrdinaryBetaDiagnosticStatementChecks passed ALL FOUR exact frozen
gates FIRST TRY at1793670457781141944-2; every finite proof module compiled
on that first invocation. This uses ACTUAL Symbol=Fin4, not natural-number
names with an inferred restriction. Arity is0,0,1,2, actual ranked precedence
is transitive, strict total, and well-founded in the displayed orientation.
The original positive steps, failed weak composite and source-support confined
witness are proved literally on Fin4. Thus the finite ranked signature and
confinement guards do not remove the LOCAL obstruction.

FiniteOrdinaryBetaDiagnostic-ACCEPTED.json
SHA9d5df2d12a2dd42cbe4ef0e2006adb8eeca0726acee705c0b6d5b7363b1a697c.
Ledger now36bundles/93fixed (FOUR diagnostic bundles),
SHAaada6711e8e17b9ab5334d9df43a51ed4a96d564f65e4857af64c2b1777a19cf.
Every earlier accepted file pin was revalidated unchanged. Zero numbered
completions; no source manuscript/register or Git change by this lane.
