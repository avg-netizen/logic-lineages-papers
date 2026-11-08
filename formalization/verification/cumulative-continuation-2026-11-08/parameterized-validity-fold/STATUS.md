# Checked: parameterized original validity fold

All four unchanged exact targets passed native Lean checking and actual
standard-axiom audits. Independent static acceptance and comparator-only
preflight preceded proof authorship. Independent postproof review remains
pending. No numbered source statement is promoted.

The packet contains seven Lean files and 17 audited declarations, including
four exact aliases. All 1,275 current local imports have successful source-
matched rows across 110 immutable native receipts. All 1,057 frozen/input
pins remain unchanged; all 1,051 broader frozen Lean inputs have successful
native matches. There are no new compiler warnings. This is cumulative
focused verification, not a fresh full-closure or full-root build.

## What is checked

- The actual binary result-fold validator satisfies its exact normalized
  numeric recurrence on every raw input and parameter. Constant-one opening
  recurses at EVERY tag-two root, including node rejection; non-tag-two roots
  normalize the old leaf on the whole original input and unchanged parameter.
- At an arbitrary fixed parameter, all-input calibration of the supplied old
  source/target/member leaves gives targetP = original target validity,
  universeP = original source validity, and sourceP = original source validity.
  This is a slice theorem, not existence of globally selected uniform leaves.
- Original constructor graphs, node(e,p)=1 and the two actual child validator
  graphs at one internally imply the actual parent validator graph at one.
  No child goodRunP=1 or semantic-calibration premise is supplied. The proof
  directly uses the accepted internal totality/application equivalence.
- Actual source conjunction acceptance internally implies target acceptance
  in any logical context, with no external calibration premise.

The semantic argument uses direct strong induction on original payload,
original strict child bounds, targetAppAcceptance/sourceAppAcceptance including
malformed applications, Boolean normalization and originalSourceImpliesTarget.
The internal file imports neither external fold calibration nor external
validity calibration proof; no evaluation-to-derivability reflection occurs.

The original result-fold state, codecs and `2*payload+1` fuel are unchanged.
Node receives [codomain,p], combine receives [d,e,functionOut,argumentOut,p],
and both children retain the same p. The older Boolean work stack has a
DIFFERENT AST and `payload+1` fuel. No AST identity is claimed. Target validity
has no universe filter. Arbitrary non-Boolean callbacks remain in recurrence.

## Boundaries and validation

This supplies a validity consumer for the parameterized result fold. It does
not select global uniform checker leaves, prove canonical representative
selection/congruence or uniform canonical/path correctness, establish an
unconditional CertifiedApplicationLift, discharge source constructor/lambda/
substitution obligations, or prove all-term accessibility or paper06 lem:id1.

- Preflight: `build-reports/1794156856052596761-6.json`.
- Exact gate: `build-reports/1794157047016014438-5.json`.
- Exact receipt SHA256: `8a07cf3d870f99adcb58c522fbf56d03c7771bc41f02d10bb1a5234bf4458aa1`.
- Actual axioms are only propext, Classical.choice and Quot.sound.
- Peak successful closure RSS: 1,176,760 KiB; component RSS: 1,081,068 KiB.
- Two failed candidates were repaired and retained locally: a supplier-name
  typo, then semantic rewrite ordering and a dependent Decidable rewrite.
  Neither repair changed a frozen statement or existing accepted source.
- Unchanged limits: 2048 MiB heap, 1536 MiB RSS, 2048 MiB minimum free,
  one thread, 90 CPU seconds, 180 wall seconds and pinned upstream cache.
- Compiler released at 2026-11-08 16:57:53 UTC; all five owned sessions ended,
  including both failures, and both shared locks were verified free.

The frozen files remain byte-identical historical records. This status and
ACCEPTANCE.json supersede their pending-proof wording. No Git, global register,
dependency, resource-policy, CI or publication action was taken.
