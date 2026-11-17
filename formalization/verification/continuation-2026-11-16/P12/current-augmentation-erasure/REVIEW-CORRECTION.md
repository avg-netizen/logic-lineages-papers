# Independent review correction: constructor-address mismatch

The reviewer withdraws the earlier approval of the CurrentAugmentationErasure certificate recipe, including its renewed recovery approval. The same-address use for specialization and transitivity was overlooked. This note preserves the old review, frozen manifests, target, and reconstructed failed proof unchanged. It is a read-only source diagnostic, not a compiled refutation, accepted theorem, or substantive-contribution credit.

## Exact source evidence

All Lean paths below are relative to `LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/` in this checkout.

- `Continuation20261116/CurrentAugmentationErasure/Definitions.lean:26-32`: `certificate` passes `K.constructorTag` to both `PrescribedSourceAxiomSpecialization.certificate` calls (lines 27 and 30) and to `transitivityCertificate` (line 32).
- `Continuation20261115/PrescribedRuntimeCallCongruence/Definitions.lean:49-54`, particularly line 52: `tags` selects its Rule12 installation's `I.current.constructorTag`. With the target's `K := tags I.previous`, this is `I.previous.current.constructorTag`.
- `Continuation20261115/UniformClosedRule12Dispatcher/Definitions.lean:20`: that membership field has the exact type `(nodes p)[constructorTag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩`.
- `Continuation20261115/UniformClosedRule13Dispatcher/Definitions.lean:20`: specialization's corresponding membership field instead has type `(nodes p)[constructorTag]? = some ⟨2,UniformClosedRule13.lineConstructor⟩`.
- `Continuation20261116/CumulativePropositionalSource/SeedProof.lean:17`: the actual specialization supplier fixes `J := I.previous.previous.current`, the Rule13 installation, not `I.previous.current`.
- `Continuation20261116/CurrentAugmentationErasure/SourceProof.lean:16-17`: the reconstructed draft updates that nested Rule13 installation with the Rule12 `constructorTag` and `h_constructor`. The dependent membership proof has arity 3 where arity 2 is required. This is not a legitimate identical-program occurrence replacement. Lines 53 and 55 repeat the wrong address in the proposed seed formulas.

The constructor programs differ already in their indexed arity. Installation membership cannot justify identifying these addresses. No compiler was invoked by this reviewer; the finding identifies a concrete source/type mismatch, rather than claiming a checked negation of the frozen target.

## Required new comparator, without weakening

Create a new package and freeze it only after fresh independent review. Give its certificate a separate Rule13 address parameter for both source-axiom specializations, retaining `K.constructorTag` solely for Rule12 transitivity. Its target must instantiate these with the actual same-source `I.previous.previous.current.constructorTag` and `(tags I.previous).constructorTag`, respectively. Derive the relevant capabilities from their existing installation membership proofs.

Retain the original Actual/source calibration, JointInstallation, installed augment node, uniform seed fuel preceding runtime choices, exact current CORE/verifier, and the unevaluated-child erasure equation. Do not add certificate-success, equal-address, computed-result, or child-evaluation assumptions. The existing lawful runtime rebase may share identical primitive programs using their actual memberships, but must leave the Rule13 and Rule12 constructors separate. Preserve the illegal reconstructed update as failed provenance.

Fresh comparator elaboration, exact proof checks and axiom audits remain required. No old acceptance transfers to the corrected package. Only this correction note was written by the reviewer.
