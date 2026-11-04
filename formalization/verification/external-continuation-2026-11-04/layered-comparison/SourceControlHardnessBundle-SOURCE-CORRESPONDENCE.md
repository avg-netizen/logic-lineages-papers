# Paper09 control-hardness: explicit chosen-model bundle for review

## Exact source statement

Hardness.tex lines 281–287, thm:control-hardness, states: “For every b, universal canonical weak comparison and strict comparison at the one fixed control Gamma_b are Pi-zero-one-complete already on ground-output sources having only ground free names and ground binders, using only the prime constants 0,S, with internal levels at most one. Moreover Gamma_b(n) mod 2 is not eventually periodic.” This bundle covers those three mathematical clauses under the explicit effective enumeration below. Numbered-source/register promotion remains a separate independent review decision.

## Enumeration and fixed control

Hardness.tex lines 235–246 fixes a primitive recursive bounded simulation for an unspecified effective enumeration of blank-input programs, with the actual transition budget. The chosen formal instance is SourceBlankMachineSimulation.program, the surjective decoding of finite binary transition tables, and boundedH, whose t argument counts actual transitions (the implementation has one extra halt observation). ExplicitEnumerationClock records surjectivity, PR and exact Run/terminal characterization, halting equivalence and literal gamma=PerturbedControl.control b boundedH. Invalid machine indices use the existing default table. This is an explicit admissible choice, not equality to all enumerations or a machine-runtime-preserving translation. Accepted blank-halting universality pays the computational completeness of this chosen model.

## Independent source languages and completeness meaning

Strict membership is SourceGammaRestrictedReduction.Member; weak membership is SourceGammaWeakCodedReduction.Member. Both independently require a decoded canonical all-ground context, typed ground sources, the recursive ground-binder/zero/successor fragment, and the exact typeSupport internal-level bound one. Both quantify every positive natural raw component valuation, as paper.tex lines 40–43 requires. Comparisons use successful finite actual assignment observations, with left<right or left≤right respectively. Neither language is defined as the image of the generated reduction.

CoREComplete is a local transparent abbreviation spelling out REPred of the complement and the universal ManyOneReducible property for every co-RE predicate on Nat. It is not a presumed Mathlib hierarchy API. This is the precise computable many-one Pi-zero-one completeness meaning used here. Each b is fixed before the query/program index; no uniform extraction from proof witnesses or joint-in-b PR evaluator is asserted.

## Canonical observation

Paper.tex lines 26–38 refers to the literal zero-history assignment. Foundations.tex lines 312–369 specifies its policy-relative tree convention, prime/application and abstraction clauses. OrdinalSyntax.defaultPolicy and AdmissibleAssignment.assignment are unchanged. denoteWith alters only the collapse control; ParametricCanonicalObservation proves agreement with any independently supplied collapse satisfying the actual maximum Equation below epsilon zero. CanonicalObservation retains AllGround/Fragment, proves successful finite observations exist, and gives their exact equivalence. This does not identify gamma with Phi. Positive raw environments are a special case of the finite natural environment in this transport theorem.

## Explicit boundaries and proof-method qualification

- Existing OriginalInput.CodedGood uses fixed Phi, a different strictness-flag tuple encoding and vacuous malformed-query truth. The new triple-coded languages reject malformed queries. No all-code equality with CodedGood is claimed; correspondence is at actual typed restricted sources with an explicit effective codec.
- The weak generated reduction uses literal K R and I L from paper.tex lines 193–201. It does not silently reuse the old magnify-based ExistentialPlan.weakPair.
- Hardness.tex lines 316–319 describes finite iteration of the PR control. The proved upper bound uses a terminating worklist and unbounded first-success search to establish Computable evaluation, not PR evaluation or a fixed numerical iteration bound. This is sufficient for the theorem's co-RE upper bound but does not certify that stronger proof wording.
- The O(e+log(b+2)) DAG discussion is a separate quantitative proof claim, not bundled here. No binary-input polynomial-time or runtime result follows.
- No unrestricted source theorem, arbitrary ordinal valuation extension, paper08 kernel-convention claim, fixed-Phi modular transfer, manuscript edit, export or register mutation is authorized by this bundle.
