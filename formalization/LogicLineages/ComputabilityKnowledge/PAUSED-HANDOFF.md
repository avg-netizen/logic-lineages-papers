# Paused formalization handoff: exponential comparison, knowledge, prediction

Paused by explicit user request for an external-agent takeover. No author,
compiler or new proof work is running in this stream. The full conclusions of
papers02,12 and14 are still pending. All current mathematical source and
acceptance facts needed below are in this repository; private Claude logs
are not required.

## Start here

1. Read `formalization/AGENTS.md` and the three source manuscripts and SOURCES
   guides in `02-exponential-comparison/`, `12-common-knowledge-necessitation/`
   and `14-complexity-of-prediction-measures/` at the repository root.
2. Read `handoff-provenance/CHECKPOINT.json` here for exact source hashes and
   status, then `Comparators/MultiplicationGadget.lean` and its independent
   `MultiplicationGadgetGate.lean`.
3. The returned200-line `MultiplicationGadgetProof.lean` is a raw, unchanged
   proposal. It has **not been elaborated**. Its first runner call was deferred
   before any Lean process:671MiB available versus the768MiB core guard. There
   are no compiler diagnostics yet and it must not be reported as proved.
4. When work is authorized to resume and resources permit, follow `formalization/README.md` for the pinned toolchain/dependency setup,
   then from `formalization/` run:

   ```sh
   python3 scripts/check.py --core-profile LogicLineages.ComputabilityKnowledge.MultiplicationGadgetProof LogicLineages.ComputabilityKnowledge.MultiplicationGadgetGate
   ```

   Compile the preserved candidate first. Repair actual diagnostics without
   changing the frozen target, domains, hypotheses or semantics. After a pass,
   check the exact independent gate and actual axiom closure; a redundant hand
   audit of every kernel-checked proof step is unnecessary. Do not add an axiom,
   sorry/admit, native_decide proof, oracle or hidden supplier premise.

The R003 Target deliberately includes THREE obligations: the numerical iff
with all eight positive witnesses, correspondence with the literal seven
source-expression pairs, and E-depth at most one on every source side. Proving
only the numerical conjunct would leave the source lemma incomplete. The
frozen comparator SHA-256 is
`a43bd3e54d1bdb9cb421ed2acde22e3390a4955bf114d4304cdaed87d0207d5e`;
the untouched proposed proof SHA-256 is
`79c9f0059d64dc1b4049635a708875d7fc1d019492fe56b0efd83b52a02545e9`.

## Already checked

- `ExponentialGapGate`: the actual positive-expression U/V construction has
  V<=U, with equality exactly when every equation of the supplied finite
  system holds at the same valuation, including the empty system. This is
  the finite-gap reduction lemma, not the full undecidability theorem.
- `RestrictedProductGate`: complete paper02 `lem:restricted-product`, with
  positive a,y,s,u,q and precisely both source upper bounds and equations.
  The accepted proof differs from the raw proposal only by fixing the D,k
  arguments of a geometric-sum rewrite. The exact gate has actual axioms
  `propext, Quot.sound`; no new premise was supplied.
- `FoundationChecks`: actual positive evaluation; depth<=2 for the collision
  compiler applied to depth<=1 equations; a concrete simultaneous-history
  anti-evader; literal source arithmetic falsehood; and full-term substitution
  semantics. Every closure stays within the standard three axioms.

The reproduction JSONs and R002 source-match/axiom output are copied into
`handoff-provenance/`, together with the exact one-line R002 repair patch.
Some older build receipts name generic per-module log
paths; their metadata is immutable but later retries may have overwritten
those original log paths. The copied R002 axiom output is preserved separately.

`GorbowFormulaSubstitution.lean` and its separate gate are Codex-written,
uncompiled candidates for capture-avoiding full-formula substitution. Their
source is saved, but no new acceptance or compiler diagnostic is asserted.

## Remaining full-target obligations

Paper02 still needs the complete effective circuit reduction and its actual
MRDP supplier, recursive normal forms/separation, one-variable decision
bounds, and the original Wilken–Weiermann admissible-assignment/vector bridge.
The existing elementary lemmas do not by themselves establish any of those
full computability classifications.

Paper12 still needs actual syntactic coding/representability, self-indexed
DCB presentation, derivability conditions and proved Loeb metatheorem, the CK
fixed-point constructor, literal KT/FS derivations and revision/consistency
proof. Its theory is Gorbow's full-language DCB/FS/KT, not Alexander's
knowing-machine theory. No presumed provability or modal oracle is accepted.

Paper14 still needs ordinary programme indices, bounded simulation and the
specified input-tape runtime convention, effective total-predictor reductions,
robust baseline, recursive-matrix/jump equivalence and the full measure/list
arguments. The semantic anti-evader alone proves no computability or runtime
claim. Mathlib Turing-degree order alone does not supply iterated jumps.

## Useful outside material

The manuscript SOURCES guides give normal scholarly references. Particularly
useful full texts are [Wilken–Weiermann2012](https://arxiv.org/abs/1203.0115v2),
[Gorbow2025](https://doi.org/10.1017/S175502032400025X), and
[Alexander–Hibbard2021](https://arxiv.org/abs/2101.12047v1). The specific Gorbow common-belief paper must not be
confused with the different2023 knower-paradoxes paper. Matiyasevich1993,
*Hilbert's Tenth Problem*, is the credited MRDP supplier; its complete local
body was not located by this bounded handoff inventory.

The public Alexander results repository's `alexander-dissertation-lean/`
contains possible generic suppliers: `Alexander/NativeSyntaxCoding.lean`,
`Alexander/FirstOrderCalculus.lean`, `Arithmetic/UniversalExecution.lean` and
`Computability.lean` (under `Alexander313/`). Current work imports NONE of
these. `handoff-provenance/outside-lean-inventory.json` provides exact
module lists and observed hashes: generic FirstOrderCalculus has two local
files, Computability four, UniversalExecution21, native proof checker29 and
SourceFixedPoint71. The larger closures include theory-specific infrastructure
and are not drop-in Gorbow suppliers. If reusing any, copy its complete local
dependency closure, record source hashes, align the same pinned Lean/Mathlib versions, and prove the exact
Gorbow/programme semantic bridge. Generic proof-tree shape recognition is not
proof-label validity; Encodable syntax is not a primitive-recursive decoder;
standard-model universal-program truth is not a PA trace proof; a numerical
knowing-machine fixed point is not the source DCB/CK fixed point.

The pinned Mathlib `ModelTheory/Encoding.lean` explicitly leaves Primcodable
syntax and syntactic-operation computability as TODO. Its Dioph/Pell material
contains useful proved ingredients but does not presently supply the full
MRDP reduction used by paper02. Do not silently turn either gap into an input
hypothesis and call the full source target complete.
