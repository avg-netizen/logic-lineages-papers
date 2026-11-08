# Original certified result-fold leaf closure

This packet freezes one supporting prerequisite toward paper 06 `lem:id1`.
It contains only Definitions, Targets and Preflight, plus static evidence.
Independent review and successful native preflight must precede proof
implementation. No proof or compiler has been run for this packet.

## Source and unchanged semantics

The source is `06-godel-t-termination-ordering/paper.tex`, lines 537-560:
the fixed subtype-closed window and original auxiliary terms, the least-code
representatives and arithmetic quotient relation, and the accessibility lemma.
This generic machine lemma is an implementation prerequisite for later
representative-fold arguments. It is not itself a numbered paper theorem,
an original source-fold invariant, or an accessibility result.

The original `InternalApplicationResultStack.openGuard`, `transition`,
`iterate`, `initial`, `fuel`, `run`, `output` and `fold` Programs are unchanged.
The original open guard combines the original application-tag test with an
exact-one root guard. Thus the hypothesis is its ACTUAL graph at zero, not
merely the raw root guard at zero or an external assertion of nonapplication.
The leaf receives the WHOLE original packed input. The combine Program is
arbitrary and is not used by the leaf transition.

The existing `InternalApplicationCertifiedResultFoldClosure.certifiedFold`
is retained literally. It is the conjunction of the actual `goodRun` graph
at one and the actual original `fold` graph at the proposed output. It is not
a new semantic predicate or a successful-run field. In particular, the raw
fold's default zero is never treated as evidence of a successful final state.
A genuine singleton containing output zero is accepted.

## One exact context-uniform internal target

For every positive body, guard and leaf Programs of arity one, combine Program
of arity four, variable type, arbitrary derivation context and symbolic input
and output, the target asks for an internal derivation of:

    (graph1 (openGuard guard) 0 value AND graph1 leaf out value)
      IMPLIES certifiedFold guard leaf combine out value.

`leafGraphs` is only an abbreviation of those two original graph formulas.
The graphs use the existing `InternalApplicationCertificateConstructors.graph1` and hence the
original arithmetic Program graph formula in the combined internal calculus.
All parameters are universally quantified. The context may be empty or
nonempty. There is no external evaluation equation, calibration, source-valid
input, output-valid input, successful run, payload bound, nonzero output,
output-size bound, or preselected auxiliary witness in the antecedent.

There is just one target and one preflight alias. A proof-only continuation
helper may later consume separate derivations of the two hypotheses, but no
second target or weakened public interface is required.

## Required internal execution route

The original fuel is exactly `succ(payload + payload)`, with payload the
actual `InternalUnpair.right` output on the original input. It is not changed
to one, enlarged, or parameterized by a new free count in the conclusion.
The future proof must construct the auxiliary graph witnesses internally:

1. Introduce the actual right-selector payload, original visit frame and
   singleton work `[visit value]`, singleton results `[out]`, and original
   initial/final live-state witnesses using internal Program graph totality.
   These are bound internal witnesses, not theorem hypotheses or semantic
   natural-number evaluations.
2. From the two leaf graphs obtain exactly one original transition from the
   live state with singleton visit work and empty results to the live state
   with empty work and singleton results. The checked
   `InternalApplicationResultStackCompositionFrameConstructorsProof.leafTransitionAt`
   supplies this from actual constructor graphs; equivalently the checked
   `InternalApplicationResultStackReturnLeafProof.leafBackward` can be used
   with the original visit/return-state constructors.
3. Apply
   `InternalApplicationResultStackCompositionBasicProof.emptyRun` for exactly
   `payload + payload` steps at empty work and singleton results. This retains
   the WHOLE terminal state and needs neither positivity of payload nor a
   bound on output. It also covers payload zero without a separate case.
4. Use
   `InternalApplicationResultStackCompositionStepProof.runFrontBackward`
   to prepend the one leaf transition. The resulting actualRun count is
   literally `succ(payload + payload)`, with original singleton visit work,
   initial results zero and final results `[out]`.
5. Apply
   `InternalApplicationCertifiedResultFoldClosureBridgeProof.certifiedFoldOfRun`
   with the internally introduced payload, visitWork and singleton-result
   graph witnesses. Its conclusion supplies BOTH actual success and actual
   fold output at the unchanged original run's own fuel.

These steps describe the intended proof obligations, not supplied proofs or
extra assumptions. The checked all-natural-input semantic goodRun calibration
must not be reflected into an internal derivation.

## Freeze and validation boundary

`FROZEN-SOURCE-PINS.json` fixes the three new Lean specifications and this
correspondence. `SOURCE-PINS.json` records the transitive local import closure
of these files and the listed prospective checked proof suppliers, together
with the manuscript, toolchain and build inputs. That inventory is static;
it is not a native compilation receipt or proof acceptance.

No original source, frozen comparator, register, build configuration or CI file
is changed. No proof files are authored. No compiler, remote build or Git
action is run. Native preflight, implementation, exact-target checks and actual
standard-axiom audits remain pending after independent review. The permitted
axioms remain `propext`, `Classical.choice` and `Quot.sound`; resource limits
and the single native compiler slot are unchanged.

This packet does not claim unguarded internal fold totality, the new source
fold invariant, representative congruence, constructor/lambda/substitution
closure, `CertifiedApplicationLift`, all-term accessibility, paper 06 `lem:id1`,
any numbered source promotion, a full-root build or remote CI success.
