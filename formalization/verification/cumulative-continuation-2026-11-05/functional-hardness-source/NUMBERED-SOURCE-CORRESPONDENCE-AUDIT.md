# Source correspondence: standard-control functional hardness

Audit date: 2026-11-05, approximately 13:29 UTC. Read-only source/definition audit; no compiler, source-register, manuscript or accepted Lean changes. This report is not independent proof acceptance.

## Recommendation

The exact candidate matches every clause of the numbered theorem `09-canonical-source-expressivity:thm:functional-hardness`. No missing mathematical clause or weakened source domain was identified. Promotion of this label is justified only after the coordinator's independent acceptance of the final assembly and its actual H10/linear-system supplier chain, followed by integration against the unchanged comparators. No new arithmetic assumption, conditional MRDP premise or stronger completeness assertion is needed by the candidate.

The checked baseline register still says pending and has null accepted declaration and comparator (`TARGETS.json:7942–7960`). That is the current registration state, not an adverse proof verdict on the new candidate. The historical remaining-obligation text is now addressed by separate candidate packages and should be reconciled only on authorized adoption. The old register did not already register a non-null formal comparator; the archived `HardnessTargets.FullFunctionalHardness` was restored unchanged, explicitly frozen, preflighted and used by this new gate.

## Source identity and literal endpoint

Paper path: `09-canonical-source-expressivity/hardness.tex`, SHA-256 `15f9e829d872b188d108a33df3b843d30b5d2be459db87dbbcfd3a1673890b7f`. This matches the baseline completion audit's source hash.

Lines 160–168 state: full universal canonical weak and strict comparison are undecidable for ground output, free-variable levels at most one and internal levels at most two; this reduction uses finitely many queries; a computable single-query reduction from the same polynomial-system unsatisfiability problem exists at internal level at most three.

`LogicLineages/OrdinalComparison/FunctionalHardnessCompletion/HardnessTargets.lean:11–14` contains all six corresponding conjuncts. The exact endpoint is `HardnessDecisionAssemblyProof.lean:23–26`; the audited alias is `HardnessDecisionStatementChecks.lean:11`. There is no extra hypothesis in the final theorem.

## Domains and canonical interpretation

In this section paths without a directory are under `LogicLineages/OrdinalComparison/`; FH abbreviates its `FunctionalHardnessCompletion/` directory.

- Ground output and the entire free-type domain: FH/HardnessDefinitions.lean:16–21,37–42. Every context of types of level at most one is included, not only the unary type used by the reduction. Both terms are actual `OriginalTerm Γ .ground`. The original kernel excludes the disjoint ranked signature: WWCanonicalPrimeDefinitions.lean:7 and SourceTerms.lean:34–45.
- Internal levels: WWSourceClassesDefinitions.lean:17–21 uses every type in the recursively collected term support, including all subtypes. SourceTypeSupportDefinitions.lean:14–24 covers function/argument/body nodes and actual constant types. The free-context bound is separate, so unused context types are not silently hidden by support.
- Standard control: paper.tex:26–35 specifies the literal zero-history original-T assignment and `Phi(t)=F_5(t+100)`. SourceCollisionCompletionDefinitions.lean:12–15 selects the literal default-policy assignment. WWDefaultPolicyDefinitions.lean:6–12 fixes the source bracketing. WWOrdinalTermSemantics.lean:34–42 and ActualCollapseDefinitions.lean:18–23 use actual collapse; ControlDefinitions.lean:16–21 fixes the exact printed Phi. No perturbed control is a parameter.
- Full valuations: FH/HardnessDefinitions.lean:20–21,41–42,54 quantify over all OriginalDomain.AdmissibleSubstitution. WWOriginalDomainDefinitions.lean:25–49 gives whole closed graded vectors with original norm bounds, matching foundations.tex:394–407. They are not restricted to polynomial lifts, chosen alignments or values realizable by closed source programs.
- Weak and strict: FH/HardnessDefinitions.lean:11–14 uses actual scalar ≤ and < separately. Ground output means there are no positive output coordinates; this agrees with foundations.tex:408–410's coordinatewise weak/coordinate-zero-strict definition, not a lexicographic order.
- Scalar fallback is not an oracle or an altered semantics: rawScalar explicitly has a zero fallback, but SourceCollisionCompletionScalarProof.lean:21–43 proves the assignment exists and its actual scalar denotation is a positive finite natural for every original ground term and every admissible substitution. Those suppliers must stay in the accepted dependency evidence.

## Polynomial source, encodings and queries

The source problem in hardness.tex:8–18 is a finite system linear in shared unknown polynomials over N[X], with fixed signed Z[X] coefficients and zero polynomials allowed. FH/UndecidabilityDefinitions.lean:7–28 represents exactly finite signed monomial rows, one shared dimension, no unknown multiplication, and checks every unknown occurrence before interpreting it. FH/Definitions.lean:34–36 permits all polynomial witnesses, including zero, and empty systems.

This is not definitionally the integer-polynomial Nat-root language used by the earlier Diophantine completion. The separately proved H10Bridge target supplies the actual computable bridge; SystemUndecidability then transfers the genuine undecidability theorem. This bridge and the source input validator remain required proof-review obligations, not assumptions hidden in FullFunctionalHardness.

FH/HardnessDefinitions.lean:8–9 packs the actual context type codes and two actual source syntax codes. SyntaxCode's raw constructor codec and typed erasure are literal source constructors (WWSourceSyntaxCodeDefinitions.lean:9–36). Its parser/typing calibration and primitive recursion have explicit targets and checked aliases (WWSourceSyntaxCodeCheckTargets.lean:6–16; WWSourceSyntaxCodeCheckStatementChecks.lean:6–10).

The source paper does not choose a particular numeral codec. The formal theorem uses this fixed effective typed de Bruijn representation. Named syntax is not an extra source primitive: existing SourceNamedSyntax, SourceNamedWeakening and SourceNamedSubstitution gates establish erasure/support/freshness/capture-avoiding substitution calibrations. The old SourceTerms.lean:13–15 comment about a pending named correspondence is not evidence that these later gates are absent. The present hardness endpoint does not additionally state a fully numerical named-text serialization theorem or an equivalence with partial algorithms promised to halt only on valid inputs. Do not advertise either as separately proved here. The ordinary decidability statement is the explicit total-computable code convention, with arbitrary answers outside the genuine bounded-input domain.

- Level two: FH/HardnessDefinitions.lean:27–31 gives one total computable list of actual bounded queries, with source unsatisfiability iff every universal query answer is true. This matches the zero-pattern proof in hardness.tex:177–193. The list length may depend on the system.
- Level three: FH/HardnessDefinitions.lean:49–54 gives one total computable actual query with the same free-type bound and internal bound three. This matches the closed-Omega construction in hardness.tex:195–223; it is not just existence of an Omega seed.
- Malformed polynomial codes are outside solvability, and actual compiled fallbacks preserve that convention. Query-decision correctness is required on every actual bounded query and nowhere else. The finite pullback uses only those actual queries (HardnessDecisionProof.lean:26–52).
- Boolean aggregation is conjunction of the actual finite answers, with true on the empty list. The reduction yields UNsatisfiability; complementation at HardnessDecisionProof.lean:53–57 obtains a satisfiability decider. The strict/weak relations are never treated as logical complements. Each receives its own contradiction (HardnessDecisionAssemblyProof.lean:11–18).

## Verification evidence and remaining acceptance work

Manifest: `FUNCTIONAL-HARDNESS-ACCEPTANCE.json` in this directory. Native gate receipt: `functional-hardness-gates/RECEIPT.json`, original receipt ID `1793884901548626869-2`. Five exact aliases passed; their actual axioms are only propext/Classical.choice/Quot.sound. The manifest records 654 local source modules matched to successful native source rows. All seven manifest source files and six comparator/semantic freeze files were rehashed for this audit and still match. No compiler was rerun for the audit.

The source-comparison review was independently repeated by the read-only `audit_printed_hardness_scope` worker. It also found no statement-level mismatch, but did not independently validate proofs or authorize adoption.

Before promotion, the coordinator must finish independent acceptance of H10 validity/adapter/full circuit/bridge, exact polynomial-system undecidability, and the FullFunctionalHardness assembly; verify the immutable source/receipt closure in the integration checkout; and update the source register and completion audit together. Ordinary non-reexported H10/Root export imports are real proof dependencies: their separate exact interface gates and all transitive source hashes must remain in the evidence, not be treated as axioms or omitted because they are not public imports.

No all-ground functional-hardness conclusion follows (hardness.tex:223). No standard-control many-one/co-RE completeness classification, runtime bound, uniform extraction algorithm from existential Diophantine representations, general Snyatkov/II5 resolution, or whole-paper completion is asserted. The separately printed perturbed-control theorem is a different label and result.
