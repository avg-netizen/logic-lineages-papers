# New comparison collection: migration and proof plan

18 November 2026. Owner requests archiving old papers and formalizing the new
set; continuation ends 19 November 2026 at 18:00 UTC. Non-force source checkpoints
at least every 30 minutes; no main merge or CI/resource/pin changes.

## Source and archive

Current source: papers/ii5-explanatory-2026-11-17 at
17377d6d02d20b26b0cf34ab50bb9d52d7c32305. Formalization base:
92459c206c0d1fc636062ce7481c6d70871f8857, which retains the verified
73709637b4997891d26ad5651628a44a8ac38392 checkpoint and later saved drafts.

Superseded editions 05–10 are moved intact under
archive/comparison-editions-pre-2026-11-17. Root compatibility symlinks preserve
source lookup; Git history and SHA-256 manifest preserve every old file.
Papers 01–04 and 11–15 are not superseded by this collection. All old Lean
proofs, counterexamples, frozen targets and failed drafts remain untouched.

## Registers

TARGETS.json remains the earlier fifteen-paper register: 178 checked,
2 inherited, 9 pending, 189 total. CURRENT-COMPARISON-TARGETS.json records
167 labeled theorem/lemma/proposition/corollary statements in papers16–20:
38,33,50,21,25 respectively. All start pending. These counts are not additive:
the old comparison statements are superseded, and reused mathematical content
is only promoted after exact source, control, domain, quantifier and dependency
comparison. Definition/example/remark environments are not counted as theorems.

## Ordered implementation

1. Paper16 persistent-mark syntax and exact marking laws, then generated
   auxiliary relation, cut/composition, decision, actual reduction orientation,
   full-type accessibility and ordinal-height suppliers. Old06's relation and
   transitivity counterexample are historical, not substitutes for this relation.
2. Paper17 explicit permitted control and preserved prefix, modular potential
   and orbit, exact repaired source interface, entry/residue arithmetic, complete
   ground comparison and functional-input hardness. Do not conflate the selected
   control with the unchanged displayed control.
3. Papers18–20: audit existing proofs against new statements, retain source-policy
   and non-strict-bound corrections, and prove genuinely new complete-profile
   observer dependencies. No mechanical transfer of old checked statuses.

Each component gets immutable semantics/comparator, source mapping, candidate
proof, native check with original serialized caps, standard-only axiom audit,
recursive source-matched evidence and independent review. Supporting definition
laws are not completion of whole numbered statements. No sorry/admit, new axiom,
oracle, native_decide, weakened endpoint or hidden supplier.

The current machine needs pinned toolchain/cache restoration. Until a native
receipt exists, every new Lean file is an unverified draft. Document preparation
and finite Python tests are not Lean verification or independent proof audits.
