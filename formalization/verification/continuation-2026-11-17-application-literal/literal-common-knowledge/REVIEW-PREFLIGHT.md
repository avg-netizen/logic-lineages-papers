# Independent preflight review — literal common knowledge

Decision: **accept the Bool-strengthened exact supporting scope** on
2026-11-17, following base commit `206a3ae0`.

## Frozen target pins

Under
`LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/Continuation20261117/LiteralCommonKnowledgeCounterexample/`:

- `Targets.lean`: `ef4bee83bdc41fac219ef1d22973580e8d673118d41490b491bc961fb355a1a7`.
- `ComparatorGate.lean`: `15743af70a254ceedbbe172f5a219228271c16fa439c6c07fb8505cc2296de75`.

The initial false-only target drafts remain preserved in
`provisional-false-only/`. The Bool strengthening precedes proof acceptance;
the accepted contract includes both original KT and its optional UBF extension.

## Source correspondence

The reviewed manuscript is `12-common-knowledge-necessitation/paper.tex`,
SHA256 `7837a0498407b5f9b2a892d6478f02f250943ae62ff69649474700cef89bb4bc`.
Its `eq:counterexample` uses the literal antecedent
`allAgentsKnow falseEquality`, without the extra top-selector equality guard.
Its final section states that both KT and KT+UBF prove this literal sentence
and the negation of its common-knowledge sentence, and neither proves that
common-knowledge sentence. The finite-iteration corollary quantifies over
external natural numbers. All these distinctions survive in the proposed
contracts and their explicit comparators.

`LiteralCollapse` concerns the chosen `closedInstance` of this literal AST,
not a code identification with the selector-guarded helper. It requires the
same original `Actual` tuple, the same installed fixed-point family, and
genuine ordinary internal HB2 and HB3 at that tuple. The first-round chosen
CK transport permits combining the literal/source equivalence with the
existing source collapse without substituting equality of sentence codes.

`LiteralFacts` quantifies over `withUBF : Bool` and retains four conclusions:
the literal theorem, its chosen-CK negation, all external finite selected
iterations, and nonprovability of that chosen CK sentence. Actual-KT
consistency is already proved for both flag values. No consistency hypothesis,
semantic truth-to-proof principle, assumption-level necessitation, or extra
HB oracle is introduced. Ordinary KT proofs may be embedded into either flag
by the original axiom/proof constructors; the false-only Barcan constructor
has an impossible Boolean equality.

`FromSelectedPresentation` consumes the unchanged
`SelectedCertifiedPresentation` contract and retains every field at one
existential witness tuple: `Actual`, syntax adequacy, code program, registry
installation, fixed-point family, and ordinary internal HB2/HB3. The new
collapse and literal facts are to be derived from those very witnesses.
No independent existential source-collapse witness may be combined with it.

## Reviewed supplier pins and boundaries

- `LiteralDefinitions.lean`: `30d159d40971ab2e172fbcf6eefbf7c65b513c828f86bc01485bb7cc3d1b7b66`.
- `SourceBaseCompletion/SelectedVerifierTargets.lean`: `29959837aac59b4115e9920c734c1c676603dc67a80a9afbe65177543d2c936a`.
- `GorbowPublishedKTTargets.lean`: `07237d5ef35627000d17df2351a9fc5fe9d7a2dfa95cefc97816f6847a5d1549`.
- First-round `ChosenCommonKnowledgeTransport/Targets.lean`: `4d9447fe713ed4c9b8ccafdc21e0e2f62d38762c7831c804fbfb0dd3a71e51af`.
- First-round `ChosenCommonKnowledgeTransport/Proof.lean`: `85f32a6a025d574e35273c0f877c890fed91f07b9b24ac92c0a4bf549408a126`.

The targets advance beyond the earlier literal direct theorem, finite
iterations, and guarded-source classification: the exact chosen CK of the
displayed literal formula gains its own collapse, negation, and nonprovability.
No duplicate full Bool literal endpoint was found in the inspected sources.

This small packet retains an explicit selected-presentation antecedent.
It alone does not establish existence of the installed source witness or
revalidate the large original source closure. The separate
`SameSourceLiteralCounterexample` packet owns that unconditional step.
Neither packet claims internal consistency, arbitrary stronger-theory
consistency, or a classification of restricted necessitation rules.

Native comparator checks, candidate proof checks, frozen-hash reconciliation,
and standard-axiom auditing remain required. This reviewer ran no compiler
or Git operation.
