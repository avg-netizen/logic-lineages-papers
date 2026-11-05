# Pending-statement register reconciliation: 5 November 2026

Historical reconciliation checkpoint: `5c98e63793b3fc821965def2292e909d4436f049`.

**163 checked, 2 inherited, 24 pending out of 189 after two targeted promotions.**

Only `08:thm:finite-source` is newly promoted by this successor after passed focused native verification. See the [exact finite-source completion audit](FINITE-SOURCE-COMPLETION-2026-11-05.md). The earlier [functional-hardness promotion](FUNCTIONAL-HARDNESS-COMPLETION-2026-11-05.md) remains historical evidence. All other 24 entries retain their prior assessments verbatim; they have not been re-audited.

This reconciles the current register and archived acceptance evidence. It does not report a new Lean run, fresh whole-proof audit, full-root build or remote CI. The [4 November audit](PENDING-STATEMENTS-2026-11-04.md) remains unchanged as historical evidence. Current source and evidence SHA-256 pins are in the [machine-readable report](PENDING-STATEMENTS-2026-11-05.json).

## Historical reconciliation corrections (before the targeted promotion)

- Add the already adopted cipher product/multiplication gate to paper02 finite hardness and paper09 functional hardness. Full MRDP/H10 remains pending.
- Add the already adopted actual Omega-seed/level-at-most-three scaled-pair gate to paper09. Its exact gate passed, but a later seeded compiler in the same archived invocation failed. The full seeded-system and level-three single-query reduction remain pending.
- Replace stale claims that source simulation, the ID1 calculus, zero-pattern treatment, corrected kernel/counter/residue source correspondence or the source Base package still need to be created. Their unproved consumers remain pending.
- Move seven already checked prerequisite references out of pending-blocker lists. The new reports retain them explicitly as checked prerequisites.
- Record the latest Snyatkov row/linear-elimination work without confusing its restricted grammar with arbitrary finite-degree composed words or full quantified BASE decision.

## Pending statements

### 02:thm:finite-bare-hardness

Existing coverage: Literal depth-two polynomial-to-comparison reductions, positive-variable framing, WW ground-domain/norm transport and co-c.e. counterexample enumeration are checked. Accepted Diophantine suppliers include pair/composition and recursion-free graph closure, binomial and bit-mask graphs, and variable-length cipher arithmetic, validity and product/multiplication. None supplies full MRDP or H10 undecidability.

Remaining: The full RE-to-Diophantine/MRDP hardness supplier is absent. The Diophantine power-graph bridge does not supply it. Depth/domain/norm conclusions must be assembled with that supplier.

Next: Freeze the exact encoded MRDP-to-comparison completeness endpoint; its missing mathematical input is full MRDP, rather than another reduction gadget.

Evidence: [DiophantinePolynomialBridge.lean](../../formalization/LogicLineages/ComputabilityKnowledge/Comparators/DiophantinePolynomialBridge.lean), [FiniteComparisonEnumerationEffectivity.lean](../../formalization/LogicLineages/ComputabilityKnowledge/Comparators/FiniteComparisonEnumerationEffectivity.lean), [WWGroundAdmissibility.lean](../../formalization/LogicLineages/ComputabilityKnowledge/WWGroundAdmissibility.lean), [ROOT-CIPHER-PRODUCT-ADOPTION.json](../../formalization/verification/local-resume-2026-11-04-six-lanes/sol1-mrdp/ROOT-CIPHER-PRODUCT-ADOPTION.json).

### 02:thm:bounded-bare-vectors

Existing coverage: Actual two-component C-vector padding, bounded norm, exact strict/weak reduction, and executable vector codes are checked.

Remaining: Undecidability still depends on finite-bare-hardness/MRDP; the padding theorem itself is not the remaining foundational gap.

Next: Reuse the complete padding/code gates when the preceding hardness endpoint is available.

Pending statement dependencies: `02:thm:finite-bare-hardness`.

Evidence: [WWBoundedVectorPadding.lean](../../formalization/LogicLineages/ComputabilityKnowledge/Comparators/WWBoundedVectorPadding.lean), [WWBoundedVectorCode.lean](../../formalization/LogicLineages/ComputabilityKnowledge/Comparators/WWBoundedVectorCode.lean).

### 02:cor:consumers

Existing coverage: Scalar identity and unary comparison, plus the entire affine one-parameter clause with actual decision programs and least positive counterexamples, are checked.

Remaining: The printed finite-valued ordinal/O-vector domain includes collapse terms. Finite-valuedness does not imply membership in the pure exponential-polynomial fragment covered by the scalar procedures. No accepted reduction/decision theorem covers that broader domain. This is an unresolved source/proof scope gap, not a proved counterexample and not merely componentwise vector bookkeeping.

Next: Resolve the exact intended domain first. Keeping the printed broad scope requires a genuine collapse-language decision bridge; narrowing it to the proved exponential fragment would be an explicit manuscript correction. Reuse the already complete affine clause.

Evidence: [AffineParameterComparison.lean](../../formalization/LogicLineages/ComputabilityKnowledge/Comparators/AffineParameterComparison.lean), [ExponentialIdentity.lean](../../formalization/LogicLineages/ComputabilityKnowledge/Comparators/ExponentialIdentity.lean), [WWGroundAdmissibility.lean](../../formalization/LogicLineages/ComputabilityKnowledge/WWGroundAdmissibility.lean), [WWGroundClasses.lean](../../formalization/LogicLineages/ComputabilityKnowledge/WWGroundClasses.lean), [EXTERNAL-CONTINUATION-2026-10-30.md](../../formalization/EXTERNAL-CONTINUATION-2026-10-30.md).

### 06:lem:structural

Existing coverage: Actual confined evaluator/scanner monotonicity and weakening, actual-limit application and substitution laws, and syntactic confinement are checked.

Remaining: The printed lemma quantifies over a natural coherent constructor family. The same-family cross-type full-tuple law needed for source application is proved at the actual fixed point, not for an arbitrary such family. No concrete counterexample has been established.

Next: Resolve the generic-family contract explicitly, then assemble substitution and literal special-application correspondence at that same scope.

Evidence: [ConfinedStructuralInterpretationTargets.lean](../../formalization/LogicLineages/OrdinalComparison/TerminationOrdering/ConfinedStructuralInterpretationTargets.lean), [ActualLimitApplicationTargets.lean](../../formalization/LogicLineages/OrdinalComparison/TerminationOrdering/ActualLimitApplicationTargets.lean), [ActualLimitSubstitutionTargets.lean](../../formalization/LogicLineages/OrdinalComparison/TerminationOrdering/ActualLimitSubstitutionTargets.lean), [STRUCTURAL-SEMANTICS-LIMITATION-20261102T1112Z.md](../../formalization/verification/external-continuation-2026-11-02/termination-ordering/STRUCTURAL-SEMANTICS-LIMITATION-20261102T1112Z.md).

### 06:thm:stable

Existing coverage: Decidability, substitution/context suppliers and exact local relational diagnostics exist.

Remaining: A checked source-confined finite-signature counterexample refutes transitivity/compatibility of the immutable local relation. Its disagreement with Kop's published theorem must be resolved; the published theorem is not thereby refuted.

Next: Identify the precise source rule/correspondence repair before attempting the unchanged stable-pair conclusion. Preserve existing relation pins and negative evidence.

Evidence: [ORDINARY-TRANSITIVITY-DIAGNOSTIC.md](../../formalization/verification/local-resume-2026-11-02/termination-ordering/ORDINARY-TRANSITIVITY-DIAGNOSTIC.md), [SOURCE-CORRESPONDENCE-STATUS.md](../../formalization/verification/local-resume-2026-11-02/termination-ordering/SOURCE-CORRESPONDENCE-STATUS.md).

### 06:lem:id1

Existing coverage: The actual finitary single-positive-operator ID1 calculus, full expanded-language PA induction, exact invariant/natural/instance rules, soundness and standard least model are checked. A concrete fixed-Gamma source presentation and conditional proof-tree-to-original-R soundness are checked. Joint-Gamma primary tests, representatives and canonical carrier are checked; these do not construct the all-term proof tree.

Remaining: The whole endpoint is ContextUniformTargets.ActualContextUniformInternalAccessibility: one fixed-S operator and closed internal derivation must cover all ambient contexts, including binder extensions. Joint-context quotient/path/direct-multiset/object-Program suppliers and the actual internal arithmetic, constructor, lambda/fundamental and all-term accessibility derivations remain pending. Fixed-Gamma presentation and conditional soundness do not supply proof-tree existence.

Next: Reuse the accepted internal calculus and context-uniform primary interface. Complete the remaining context-uniform source presentation, then construct the internal all-term derivation at ActualContextUniformInternalAccessibility; do not redefine the judgment or weaken it to fixed Gamma.

Evidence: [PositiveArithmeticLeastSetTargets.lean](../../formalization/LogicLineages/OrdinalComparison/TerminationOrdering/PositiveArithmeticLeastSetTargets.lean), [PositiveArithmeticLeastSchemasTargets.lean](../../formalization/LogicLineages/OrdinalComparison/TerminationOrdering/PositiveArithmeticLeastSchemasTargets.lean), [SourceApplicativeSubstitutionTargets.lean](../../formalization/LogicLineages/OrdinalComparison/TerminationOrdering/SourceApplicativeSubstitutionTargets.lean), [SourceGroundLambdaTowerTargets.lean](../../formalization/LogicLineages/OrdinalComparison/TerminationOrdering/SourceGroundLambdaTowerTargets.lean), [ROOT-R001-COMPONENT-ADOPTION.json](../../formalization/verification/local-resume-2026-11-04-six-lanes/sol2-id1/ROOT-R001-COMPONENT-ADOPTION.json), [ROOT-R002V2-COMPONENT-ADOPTION.json](../../formalization/verification/local-resume-2026-11-04-six-lanes/sol2-id1/ROOT-R002V2-COMPONENT-ADOPTION.json), [ROOT-R004-COMPONENT-ADOPTION.json](../../formalization/verification/local-resume-2026-11-04-six-lanes/sol2-id1/ROOT-R004-COMPONENT-ADOPTION.json), [ContextUniformTargets.lean](../../formalization/LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/ContextUniformTargets.lean).

### 06:thm:upper

Existing coverage: The whole fixed-family source simulation lemma is adopted: one source-shaped translation family has primitive-recursive numeric calibration and positive original-source paths at the same source-anchored type universe. The simulation theorem adds no ID1 or ordinal-analysis premise.

Remaining: The genuine ID1 accessibility proof and Pohlers-style inductive-norm/ordinal stage-bound extraction below Bachmann-Howard are not supplied.

Next: Reuse the checked source simulation. Prove the pending context-uniform internal ID1 accessibility endpoint and exact cited inductive-norm/ordinal stage-bound extraction below Bachmann-Howard, then assemble the upper bound.

Checked prerequisites to reuse: `06:lem:simulation`.

Pending statement dependencies: `06:lem:id1`.

Evidence: [NumberedConfinedSourceSimulationTargets.lean](../../formalization/LogicLineages/OrdinalComparison/TerminationOrdering/NumberedConfinedSourceSimulationTargets.lean), [SourceArithmeticAccessibilityTargets.lean](../../formalization/LogicLineages/OrdinalComparison/TerminationOrdering/SourceArithmeticAccessibilityTargets.lean), [ROOT-SOURCE-ADOPTION.json](../../formalization/verification/local-resume-2026-11-04-six-lanes/sol1-simulation/ROOT-SOURCE-ADOPTION.json).

### 06:lem:realclosure

Existing coverage: Literal native beta/context/reduction and iteration-edge suppliers exist.

Remaining: A typed ordinal realization relation with backward/order/countable-supremum closure and the lambda fundamental lemma is not proved. Full ranks also depend on well-foundedness of the intended source relation.

Next: Establish the exact relation and well-foundedness scope before the ordinal realization fundamental theorem.

Pending statement dependencies: `06:thm:stable`.

Evidence: [NativeBetaCasesTargets.lean](../../formalization/LogicLineages/OrdinalComparison/TerminationOrdering/NativeBetaCasesTargets.lean), [NativeIterationEdgesTargets.lean](../../formalization/LogicLineages/OrdinalComparison/TerminationOrdering/NativeIterationEdgesTargets.lean).

### 06:thm:iteration

Existing coverage: The actual native carrier and all three iteration edges are checked.

Remaining: The full-prefix transfinite orbit realization proof, including limits for nonmonotone functions, is absent; reduction edges alone do not prove it.

Next: Use the existing edges in one realization theorem once realclosure is available; preserve the entire-prefix limit clause.

Pending statement dependencies: `06:lem:realclosure`.

Evidence: [NativeCarrierTargets.lean](../../formalization/LogicLineages/OrdinalComparison/TerminationOrdering/NativeCarrierTargets.lean), [NativeIterationEdgesTargets.lean](../../formalization/LogicLineages/OrdinalComparison/TerminationOrdering/NativeIterationEdgesTargets.lean).

### 06:lem:primitives

Existing coverage: Native carrier strictness and application closure already support the finite cap's reduction inequalities.

Remaining: Zero/successor/omega ordinal realization and the all-iterate cap conclusion have not been assembled at the manuscript's realization contract.

Next: Assemble the native primitive realizers with the rank/realization infrastructure; avoid reproving carrier edges.

Pending statement dependencies: `06:lem:realclosure`.

Evidence: [NativeCarrierTargets.lean](../../formalization/LogicLineages/OrdinalComparison/TerminationOrdering/NativeCarrierTargets.lean), [NativeIterationEdgesTargets.lean](../../formalization/LogicLineages/OrdinalComparison/TerminationOrdering/NativeIterationEdgesTargets.lean).

### 06:thm:height

Existing coverage: Native carrier/iterator syntactic ingredients exist.

Remaining: Both the individual upper bound and full lower realization/calibration are incomplete. The Simmons/helpfulness/cofinal-collapse calibration to BH is an additional mathematical supplier, not supplied by finite kernel or arithmetic checker proofs.

Next: Finish the shared realization and ID1/ordinal suppliers, then compile the exact finite extractor family and cofinality argument.

Pending statement dependencies: `06:thm:upper`, `06:thm:iteration`, `06:lem:primitives`.

Evidence: [NativeIterationEdgesTargets.lean](../../formalization/LogicLineages/OrdinalComparison/TerminationOrdering/NativeIterationEdgesTargets.lean), [NativeCarrierTargets.lean](../../formalization/LogicLineages/OrdinalComparison/TerminationOrdering/NativeCarrierTargets.lean).

### 08:thm:snyatkov

Existing coverage: The accepted source-row packages provide original term graphs and Boolean/binder-position-preserving row introduction; bounded substitution and finite branches; total signed unit-slope translation and restricted hyper-collision; nested translation and both plain-Phi windows; and effective elimination of a name occurring only linearly in the restricted row grammar. The linear step preserves arbitrary signed coefficients, original domains, correlated nonlinear terms at other names and exact eliminated-name support, with primitive-recursive numeric code.

Remaining: The complete arbitrary quantified BASE decision theorem remains unproved. General nonlinear anchors, active-hyper source-case assembly, general affine substitution inside nonlinear arguments, dominant boundaries, exhaustive branch selection and global decreasing quantified-block induction remain pending. Restricted row introduction and linear elimination do not establish the full source existential normal form or expanded elimination closure.

Next: Reuse the accepted row syntax, finite-window and linear-elimination compilers. Close the remaining nonlinear source cases and exhaustive decreasing elimination induction, then prove EffectiveSourceExistentialNormalForm, EffectiveExpandedElimination and FullSourceDecision.

Evidence: [SnyatkovUnaryDecisionTargets.lean](../../formalization/LogicLineages/OrdinalComparison/LayeredComparison/SnyatkovUnaryDecisionTargets.lean), [SnyatkovDivisibilityTargets.lean](../../formalization/LogicLineages/OrdinalComparison/LayeredComparison/SnyatkovDivisibilityTargets.lean), [SnyatkovHyperCollisionTargets.lean](../../formalization/LogicLineages/OrdinalComparison/LayeredComparison/SnyatkovHyperCollisionTargets.lean), [PAUSED-AFTER-FIVE-ROUNDS-2026-11-04.md](../../formalization/verification/local-resume-2026-11-03/layered-comparison/PAUSED-AFTER-FIVE-ROUNDS-2026-11-04.md), [ACCEPTANCE.json](../../formalization/verification/cumulative-continuation-2026-11-04-second/linear-rows/ACCEPTANCE.json), [SOURCE-CORRESPONDENCE.md](../../formalization/verification/cumulative-continuation-2026-11-04-second/linear-rows/SOURCE-CORRESPONDENCE.md), [FROZEN-TARGETS.json](../../formalization/verification/cumulative-continuation-2026-11-04-second/linear-rows/FROZEN-TARGETS.json), [SOURCE-CLOSURE.json](../../formalization/verification/cumulative-continuation-2026-11-04-second/linear-rows/SOURCE-CLOSURE.json).

### 08:lem:uniform

Existing coverage: The degree-two separation base and higher counter leader/recognition suppliers are checked. The explicitly corrected paper08 limit-part process, genuine signed-domain recursion, full counter theorem and effective residues are now adopted; the original incompatible wording remains historical negative evidence.

Remaining: The full arbitrary-rank quantitative separation induction with the manuscript's printed region and constants is not proved. It must be connected to the accepted corrected limit-part process and genuine signed domains; adoption of those suppliers does not itself prove this uniform induction.

Next: Freeze and prove the entire rank-at-least-three statement under the now explicit corrected source convention, retaining the printed C_d/T_d, growing retained masses and every regional hypothesis. Reuse the accepted kernel/counter package.

Checked prerequisites to reuse: `08:lem:kernel-recursion`.

Evidence: [QuadraticSeparationTargets.lean](../../formalization/LogicLineages/OrdinalComparison/QuadraticSeparationTargets.lean), [CounterLeaderComparisonTargets.lean](../../formalization/LogicLineages/OrdinalComparison/CounterLeaderComparisonTargets.lean), [ROOT-SOURCE-ADOPTION.json](../../formalization/verification/local-resume-2026-11-04-six-lanes/sol4-kernels/ROOT-SOURCE-ADOPTION.json).

### 08:lem:guards

Existing coverage: Corrected-source kernel recursion, the whole counter expansion/collision/order theorem and effective residue suppliers are adopted. They cover numerical comparison dependencies, not the complete arbitrary-word compiler.

Remaining: No complete effectual comparison compiler for arbitrary composed words with ordered raw-variable guards, all signed domains and a verified decreasing recursion measure is present.

Next: Prove the whole ordered-word guard compiler, using the source's two-part termination measure and exact shared-variable semantics.

Checked prerequisites to reuse: `08:lem:counter`.

Pending statement dependencies: `08:lem:uniform`.

Evidence: [CounterLeaderComparisonTargets.lean](../../formalization/LogicLineages/OrdinalComparison/CounterLeaderComparisonTargets.lean), [CounterSourceTheoremTargets.lean](../../formalization/LogicLineages/OrdinalComparison/CounterSourceTheoremTargets.lean), [ROOT-SOURCE-ADOPTION.json](../../formalization/verification/local-resume-2026-11-04-six-lanes/sol4-kernels/ROOT-SOURCE-ADOPTION.json).

### 08:lem:row

Existing coverage: The whole counter expansion/collision/order theorem is adopted under the explicit corrected source process. Common-head/balanced compilers and the later Snyatkov linear-row compiler solve distinct restricted grammars, not arbitrary finite-degree word rows.

Remaining: Arbitrary word-linear ranked cancellation, all generated guards and the well-founded top-level rank measure remain unproved. The common-head/balanced compilers do not establish this word-language lemma.

Next: Build the exact ranked row transformation after the word-guard compiler, preserving current-occurrence growth provenance.

Checked prerequisites to reuse: `08:lem:counter`.

Pending statement dependencies: `08:lem:guards`.

Evidence: [CounterSourceTheoremTargets.lean](../../formalization/LogicLineages/OrdinalComparison/CounterSourceTheoremTargets.lean), [CommonLayerCompilerTargets.lean](../../formalization/LogicLineages/OrdinalComparison/LayeredComparison/CommonLayerCompilerTargets.lean), [BalancedTypedCompilerTargets.lean](../../formalization/LogicLineages/OrdinalComparison/LayeredComparison/BalancedTypedCompilerTargets.lean), [ROOT-SOURCE-ADOPTION.json](../../formalization/verification/local-resume-2026-11-04-six-lanes/sol4-kernels/ROOT-SOURCE-ADOPTION.json), [SOURCE-CORRESPONDENCE.md](../../formalization/verification/cumulative-continuation-2026-11-04-second/linear-rows/SOURCE-CORRESPONDENCE.md).

### 08:thm:existential

Existing coverage: Corrected-source kernel/counter evaluation and effective residue theorems are adopted. Restricted Snyatkov source rows now have correlated linear-name elimination with exact support and primitive-recursive code. That grammar is narrower than this theorem's finite-degree composed-word language.

Remaining: The complete closed existential procedure on the printed finite-degree word language is still absent. Word guards and ranked cancellation remain pending, as does their end-to-end assembly with the checked residue suppliers, finite exceptions and correlated Presburger elimination. The restricted source-row linear eliminator is not a whole-word elimination theorem.

Next: Build the complete word-language procedure with decreasing raw-variable count, reusing the checked corrected residues and arithmetic components only where their exact grammars match. Free-parameter or arbitrary alternating-quantifier elimination for the word language is not required by this closed-sentence theorem.

Checked prerequisites to reuse: `08:lem:kernel-residues`.

Pending statement dependencies: `08:lem:guards`, `08:lem:row`.

Evidence: [FiniteKernelRecursionTargets.lean](../../formalization/LogicLineages/OrdinalComparison/FiniteKernelRecursionTargets.lean), [KernelCounterResidueTargets.lean](../../formalization/LogicLineages/OrdinalComparison/KernelCounterResidueTargets.lean), [ROOT-SOURCE-ADOPTION.json](../../formalization/verification/local-resume-2026-11-04-six-lanes/sol4-kernels/ROOT-SOURCE-ADOPTION.json), [SOURCE-CORRESPONDENCE.md](../../formalization/verification/cumulative-continuation-2026-11-04-second/linear-rows/SOURCE-CORRESPONDENCE.md).

### 08:thm:graphs

Existing coverage: Exact prefix/kernel identities, evaluators and the original-process-to-companion bridge are adopted for the explicitly corrected limit-part convention and genuine signed domains.

Remaining: The total polynomial-head graph compiler, finite exceptions, nesting/addition flattening and full functional graph correctness have not been assembled at this word-language contract.

Next: Reuse the accepted corrected kernel/process bridge and construct the full polynomial-head graph translation, with finite exceptions, nesting/addition flattening and quantified equations over the same original shared variables. No new source-convention decision is needed for the already adopted kernel statements.

Checked prerequisites to reuse: `08:lem:kernel-recursion`.

Evidence: [FiniteKernelRecursionTargets.lean](../../formalization/LogicLineages/OrdinalComparison/FiniteKernelRecursionTargets.lean), [CounterSourceTheoremTargets.lean](../../formalization/LogicLineages/OrdinalComparison/CounterSourceTheoremTargets.lean), [ROOT-SOURCE-ADOPTION.json](../../formalization/verification/local-resume-2026-11-04-six-lanes/sol4-kernels/ROOT-SOURCE-ADOPTION.json).

### 08:thm:leveltwo

Existing coverage: Actual source assignment and generated-coordinate invariants are established in the source foundations.

Remaining: The internal-level-two polynomial-head classification/consumer and complete counterexample-to-word-graph decision chain remain unassembled; the word decision and graph suppliers are also incomplete.

Next: Complete the source polynomial-head classifier and compose graph translation with the closed existential solver.

Pending statement dependencies: `08:thm:graphs`, `08:thm:existential`.

Evidence: [WWSourceFinitePositiveTargets.lean](../../formalization/LogicLineages/OrdinalComparison/WWSourceFinitePositiveTargets.lean), [paper.tex](../../08-multivariate-collapse-comparison/paper.tex).

### 08:thm:common

Existing coverage: The entire actual common-head grammar-to-literal-BASE compiler is checked: semantic truth, shared original valuation, no new raw variables and unconditional code computability.

Remaining: The theorem ALSO asserts decision of arbitrary Boolean/quantified combinations, which still needs full Snyatkov. The literal same-free-variable clause should get an exact support-equality wrapper; current common-head gate guarantees containment and shared identities.

Next: Reuse the complete compiler, add an exact-variable padding wrapper if needed, and compose with the single shared BASE decision supplier.

Pending statement dependencies: `08:thm:snyatkov`.

Evidence: [CommonLayerCompilerTargets.lean](../../formalization/LogicLineages/OrdinalComparison/LayeredComparison/CommonLayerCompilerTargets.lean), [CommonLayerComparisonTargets.lean](../../formalization/LogicLineages/OrdinalComparison/LayeredComparison/CommonLayerComparisonTargets.lean).

### 08:thm:balanced

Existing coverage: The later external work supplies the entire raw/typed balanced compiler, actual shared-certificate semantics, unconditional output computability and exact syntactic free-variable equality. Older local notes listing collection/box/compiler gaps are superseded.

Remaining: Only the theorem's Boolean/quantified decision conclusion still requires the full Snyatkov supplier, plus an end-to-end source gate joining that solver to the compiler. Do not rebuild balanced collection, guards or finite boxes.

Next: Adopt the whole theorem after the BASE solver, using BalancedExactVariables as the completed translation endpoint.

Pending statement dependencies: `08:thm:snyatkov`.

Evidence: [BalancedRawCompilerTargets.lean](../../formalization/LogicLineages/OrdinalComparison/LayeredComparison/BalancedRawCompilerTargets.lean), [BalancedTypedCompilerTargets.lean](../../formalization/LogicLineages/OrdinalComparison/LayeredComparison/BalancedTypedCompilerTargets.lean), [BalancedExactVariablesTargets.lean](../../formalization/LogicLineages/OrdinalComparison/LayeredComparison/BalancedExactVariablesTargets.lean).

### 12:thm:collapse

Existing coverage: The exact source Base/syntax apparatus, self-indexed proof calibration and same-parameter selected-agent/KT consistency pair are adopted as lem:three and thm:consistency. Actual diagonal and conditional Lob suppliers, retained-parameter closed-instance CK equations, bounded-range and PA addition laws are supporting components.

Remaining: Actual internal HB2/HB3 for the chosen source provability predicate, identification of the chosen source CK within that same construction, and the full selected collapse derivation remain pending. Source Base availability and self-indexed calibration are already adopted; they do not discharge internal HB or the chosen-CK identification. The conditional Lob theorem still assumes its HB instances.

Next: Reuse the adopted source Base and self-indexed calibration. Establish actual internal HB2/HB3 and the chosen CK correspondence, then assemble the source collapse without proof-oracle premises.

Checked prerequisites to reuse: `12:lem:three`.

Evidence: [GorbowPublishedLobReductionTargets.lean](../../formalization/LogicLineages/ComputabilityKnowledge/GorbowPublishedLobReductionTargets.lean), [GorbowUniformCommonKnowledgeTargets.lean](../../formalization/LogicLineages/ComputabilityKnowledge/GorbowUniformCommonKnowledgeTargets.lean), [ROOT-SOURCE-ADOPTION.json](../../formalization/verification/local-resume-2026-11-04-six-lanes/claude/ROOT-SOURCE-ADOPTION.json), [BaseTargets.lean](../../formalization/LogicLineages/ComputabilityKnowledge/SourceBaseCompletion/BaseTargets.lean).

### 12:corollary-3

Existing coverage: Uniform retained-parameter common-knowledge fixed-point equations exist. The same actual source Base/syntax and selected-agent/consistency package has now been adopted; the fixed-point supplier is not the original D-equivalence.

Remaining: The original D-equivalence to CK_A(b) still requires identification of the chosen CK within the adopted source Base construction and the pending source collapse theorem. A fixed-point supplier alone is not this equivalence.

Next: Assemble this short logical consumer once the actual collapse/source CK contract is available.

Pending statement dependencies: `12:thm:collapse`.

Evidence: [GorbowUniformCommonKnowledgeTargets.lean](../../formalization/LogicLineages/ComputabilityKnowledge/GorbowUniformCommonKnowledgeTargets.lean), [ROOT-SOURCE-ADOPTION.json](../../formalization/verification/local-resume-2026-11-04-six-lanes/claude/ROOT-SOURCE-ADOPTION.json).

### 12:thm:selector

Existing coverage: Actual published KT/FS/veracity syntax is available, and whole-source lem:three/thm:consistency are adopted in one source Base construction.

Remaining: The full-language source-KT selector classification still depends on the source collapse theorem and chosen-CK identification within the already adopted Base. The completed consistency pair is not the selector classification.

Next: Compose actual veracity/atomic contradiction truth with the source collapse and prove both selector equivalences.

Pending statement dependencies: `12:thm:collapse`.

Evidence: [GorbowPublishedKTDefinitions.lean](../../formalization/LogicLineages/ComputabilityKnowledge/GorbowPublishedKTDefinitions.lean), [GorbowPublishedAtomicTruthTargets.lean](../../formalization/LogicLineages/ComputabilityKnowledge/GorbowPublishedAtomicTruthTargets.lean), [ROOT-SOURCE-ADOPTION.json](../../formalization/verification/local-resume-2026-11-04-six-lanes/claude/ROOT-SOURCE-ADOPTION.json).

### 12:cor:finite

Existing coverage: The actual KT proof system already has the CLOSED theorem-only knowledge-necessitation constructor.

Remaining: The source counterexample theta theorem is not yet established through the collapse/selector chain. No new internally quantified iteration theorem is needed: r is an external fixed natural number.

Next: After the source theta theorem, induct externally using the existing closed rule; avoid general recursive-graph or internally quantified iteration work for this corollary.

Pending statement dependencies: `12:thm:selector`.

Evidence: [GorbowPublishedKTDefinitions.lean](../../formalization/LogicLineages/ComputabilityKnowledge/GorbowPublishedKTDefinitions.lean).
