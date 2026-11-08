# Parameterized original validity fold: frozen prerequisite

This packet freezes definitions and four exact targets only. There are no
proof files, compiler runs, acceptance claims or numbered-source promotions.
It specializes the existing parameterized result fold to Boolean validity and
retains the original source and target predicates as semantic comparators.

## Source and AST boundary

Paper 06, `06-godel-t-termination-ordering/paper.tex`, lines 537-549, specifies
the original well-typed reductions. Lines 551-556 retain the original quotient,
least-code representatives and arithmetic relations H/R; lines 558-560 state
`lem:id1`. This packet is only a prerequisite for that source programme.
The machine-success predicate goodRunP is not the paper's relation H.

The new finite AST wrappers use only existing Programs and wiring:

- `openingGuardP` is ALWAYS `InternalLessThan.constantOne 2`. Every original
  tag-two root opens. Node failure must never close that opening guard.
- `leafP oldLeaf` is `GorbowVerifierNormalization.normalize oldLeaf`, applied
  to `[wholeOriginalPackedInput,p]`. Every non-tag-two root uses that whole leaf.
- `nodeAtP node` wires quinary coordinates `[1,4]`, namely `[codomain,p]`.
- `combineP node` is the exact-one conjunction of that node test with the
  exact-one conjunction of coordinates 2 and 3, function then argument.
  Node rejection therefore produces zero at combine, not fallback to a leaf.
- `validatorP` is literally the existing parameterized `foldP` with these
  three callbacks. Its state, codecs, iterator and original `2*payload+1`
  fuel are unchanged. Parameter, whole packed type and output sizes add no fuel.
- `targetP oldTarget` uses node `constantOne 2` and has no universe filter.
  `universeP oldSource member` uses the original membership callback as node.
  `sourceP` is the concrete conjunction of target and universe Programs.

This result-fold AST is DIFFERENT from the older Boolean work-stack validator,
whose fuel is `payload+1`. There is no AST equality or definitional identity
claim between them. The correspondence is semantic equality with the unchanged
`InternalOriginalStepGuard.targetValidityValue` and `sourceValidityValue`.
No nonexistent generic `validatorValue` is used as a comparator.

## Four exact targets

0. **External all-input numeric recurrence.** The actual bounded Program's
   result equals the normalized conjunction of node(codomain,p), function
   child result and argument child result on every tag-two root. All other
   roots normalize oldLeaf(wholeInput,p). The callbacks and p are arbitrary;
   malformed inputs and non-Boolean callback outputs remain in scope.
1. **External slice calibration.** For every original n, arity, symbol list,
   S, Gamma and arbitrary fixed p, assume the supplied old source/target
   binary leaves agree with the original predicates on ALL numeric inputs
   at that p, and the binary member leaf agrees with original membership
   at that p. Then targetP equals original target validity, universeP equals
   original source validity, and sourceP equals original source validity on
   EVERY raw input at p. These are semantic hypotheses, not internal rules.
   This target neither selects nor proves existence of globally uniform
   binary leaves across contexts, windows, or parameters.
2. **Internal application closure.** For arbitrary body, variable type,
   context and Programs, use the original application constructor graphs,
   node(e,p)=1, and each actual child validator graph at output one to derive
   the actual parent validator graph at output one. There are no goodRunP=1
   premises, semantic calibration premises, assumed validity, enlarged fuel,
   or substituted code encodings. The same p occurs throughout.
3. **Internal source-to-target.** Recover targetP acceptance from the actual
   sourceP conjunction at arbitrary symbolic input and p. No calibration or
   external source-implies-target fact is needed for this internal target.

## Required proof route and dependency boundary

The external recurrence follows by specializing the separately frozen
parameterized bounded result-fold calibration and semantic fold equation.
Normalize the leaf and both conjunction levels using their existing exact
all-input evaluation laws. The constant-one opening guard is indispensable:
a failed node must yield zero, never invoke oldLeaf on an application root.

For external calibration use direct strong induction on the ORIGINAL numeric
payload, generalized over whole packed inputs with that payload. On tag two,
`InternalApplicationValidityStackStateProof.applicationPayloadBound` supplies
strictly smaller child payloads. The existing `targetAppAcceptance` and
`sourceAppAcceptance` in `InternalApplicationValidityStackInvariantProof`
cover malformed applications as well as decoded ones. Non-tag-two roots use
the given whole-input leaf calibration. The existing `boolNormalized` in
`InternalApplicationValidityCalibrationProof` removes exact-one normalization
of the original Bool.toNat predicates. Finally its `originalSourceImpliesTarget`
and the actual conjunction evaluation prove sourceP agreement. Neither
calibration of the old Boolean stack nor an AST identification is substituted
for this direct argument.

For internal application closure, specialize the separately frozen pending
`ActualOriginalParameterizedResultFoldApplicationEquation` with opening G
constant one, normalized old leaf and the concrete combine Program. Prove
G(parent,p)=1 by the original constant Program rules. The given child graphs
and internally proved parameterized fold totality supply the original parent
fold/combine equation WITHOUT supplied child-success graphs. Node acceptance
and the two one outputs yield the actual combine output one by ordinary
composition and conjunction derivations. External calibration cannot supply
an internal derivation. Source-to-target uses only conjunction recovery.

The parameterized result-fold totality proofs are under separate final review.
Only their stable definitions, targets and preflight are pinned here, not their
mutable proofs or acceptance metadata. The same policy applies to pending
parameterized fold-calibration and certified-closure specification suppliers.
Selected already accepted semantic, normalization, graph and conjunction
suppliers and their import closures are pinned as proof-route evidence.

## Freeze, gates, and exclusions

`FROZEN-SOURCE-PINS.json` covers the three new Lean specification files and this
correspondence. `SOURCE-PINS.json` covers the full local import closure of
specification and selected stable supplier roots, the manuscript and unchanged
build inputs. `STATIC-CHECKS.json` records static syntax, comparator coverage,
closure and hash verification only; it is not Lean elaboration or acceptance.
`FROZEN-SPECIFICATION.json` identifies the exact frozen contract.

Next gates: independent frozen-byte review; coordinator-authorized comparator
preflight; acceptance of the pending parameterized fold suppliers; separately
authorized proof authorship; exact frozen-type aliases and actual standard
axiom audits. No compiler slot was requested or held. The unchanged profile is
2048 MiB heap, 1536 MiB RSS, 2048 MiB minimum free, one thread, 90 CPU seconds,
180 wall seconds, pinned upstream cache and `scripts/check.py`. Hard cutoff:
2026-11-08 18:00 UTC. Allowed axioms remain `propext`, `Classical.choice`,
and `Quot.sound` only.

No globally selected uniform source/target leaf package, internal semantic
reflection, full uniform canonical/path correctness, canonical representative
selection, unconditional CertifiedApplicationLift, source constructor/lambda/
substitution proof, all-term accessibility or paper06 `lem:id1` completion is
claimed. No accepted-source edit, register promotion, dependency/CI change,
full-root build, remote CI or Git action is part of this packet.
