# Original guarded application-step transport

This two-target supporting packet isolates the function-side auxiliary
application rule in paper 06, `paper.tex` lines 537-549, toward `lem:id1`
at lines 558-560. It retains the original numeric terms, type codes,
certificate numbering and internal arithmetic calculus. It does not assert
the whole lemma, a quotient-edge congruence theorem, or a certified path lift.
The existing source register and every prior frozen file are unchanged.

## Literal selected programs

The only leaf bundle is `Data` with `oldValidity`, `member`, and `oldStep`.
These are finite `Program` ASTs with no proof or correctness fields.

- `validity data` is literally `recursiveData data.oldValidity data.member`.
- `endpoint data` is literally the structural endpoint using that validity
  and the same member leaf.
- `normalizedCore data` is literally the checked repeat-then-old-step
  `InternalApplicationStepPeel.checker` using that endpoint and oldStep.
- `stepChecker data` is literally `InternalOriginalStepGuard.checker`
  with that validity and normalized core.

Thus a semantic coincidence of two different programs cannot substitute
for an internal graph transport. Both original and lifted acceptance use
the very same guarded checker. The source recursive validity includes its
actual target/universe conjunction. Target recursive validity has only the
original packed decoder and no source-universe filter.

All three leaf calibrations cover every natural input, at fixed signature,
symbols, arbitrary finite window S, Gamma and precedence table. The selected
calibration also covers every natural input of the constructed recursive
validity, endpoint and guarded step. In particular it preserves failures of
the source universe decoder and packed target decoder, unequal outer types,
malformed raw certificates and original zero/one outputs. Calibration is an
external theorem and supplies no symbolic internal inference.

## Exact internal premises and conclusion

`liftPremises` uses the already frozen closure premise formula unchanged:

1. `graph2 consCode arrow d e` for the original arrow type code;
2. output-one acceptance of the exact selected structural endpoint at
   `[d,e,s,t,a]`;
3. `graph4 application sourceApp d e s a`;
4. `graph4 application targetApp d e t a`;
5. `graph1 stepLift liftedStep k`.

The application graphs use the original raw constructor, which removes the
child outer tags. The endpoint must derive those actual child tag graphs;
they are not new assumptions. The original `stepLift` prefixes the unchanged
function-child position to the original path while preserving its payload.
No decode or well-formedness assumption is imposed on k.

**ActualOriginalGuardedApplicationStep** derives, in the unchanged
`InternalCalculus.Derivation body []`, acceptance of
`[sourceApp,targetApp,liftedStep]` by the exact `stepChecker data` from
`liftPremises` and acceptance of `[s,t,k]` by that same checker. All leaf ASTs,
positive bodies, variable types and symbolic inputs are arbitrary. This is
the minimal accepted-step direction required by the source rule, not a claim
of unrestricted full-output equivalence for an arbitrary outer wrapper.

**ActualOriginalSelectedApplicationStep** selects one leaf bundle for each
fixed original signature, S, Gamma and table, before quantifying every body,
variable type, symbolic type code, endpoint and certificate. It provides both
leaf calibration and exact constructed-program calibration, together with
the preceding internal rule for that literal selected checker. It does not
choose a new program after observing a term or a proof.

## Required proof route, not extra premises

The existing structural-endpoint factorization derives all original child
tag graphs. The accepted normalized-core transport then carries the core's
output-one graph from the original triple to its actual lift. The active
`InternalApplicationValidityClosure` proof must supply the two lifted
validity graphs from the exact original endpoint and application graphs.
The actual application constructors supply codomain outer-tag graphs for
both applications. Original guard introduction then reinstates the outer
source validity, target validity and common type test. Neither application
validity nor a `CertifiedApplicationLift` is added as a theorem premise.

External selected calibration composes the checked recursiveData calibration,
structural endpoint calibration, normalized-core calibration and original
outer-guard calibration. Existing original validity, member and numeric-step
program existence theorems provide the leaf selection. These steps prove
calibration of concrete definitions, not an identification of internal graphs
from equal natural evaluations.

The checked `InternalTypedEdgePresentation` was inspected but is not imported
or extended by this packet. Its old existential package permits arbitrary
calibrated validity, so it cannot alone supply this recursive-validity
selection. A later typed integration must construct its data with this exact
recursive validity and reuse parameterized presentation/calibration helpers.
No representative application congruence or typed-edge-to-lift theorem is
being asserted here.

## Freeze and acceptance boundaries

Definitions imports only the stable closure Definitions. Targets imports only
these new Definitions. Comparator-only Preflight imports only Targets. No
candidate proof file exists at this freeze. Stable closure Definitions and
Targets are pinned, but the actively repaired closure proof is not pinned or
claimed accepted. Its acceptance is a prerequisite of this packet's later
proof gate, not a reason to assume its conclusion.

Independent review and serialized native preflight must precede proof
authorship. The current closure worker owns the sole compiler slot. This
preparation launches no compiler, author or Git action. Later checks must use
the unchanged check.py profile: one worker, heap 2048 MiB, RSS 1536 MiB,
minimum free 2048 MiB, CPU 90 seconds and wall 180 seconds, cached upstream
dependencies only. Exact statement aliases and actual axiom closure are
required; only propext, Classical.choice and Quot.sound are allowed.

Excluded claims: representative congruence; typed-edge/path assembly;
joint-context uniformity; outer pathValue malformed-object handling;
CertifiedApplicationLift; source multiset, constructor, lambda, substitution
or fundamental derivations; all-term accessibility; numbered source
promotion; full-root build; remote CI; publication.
