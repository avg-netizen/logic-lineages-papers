Actual symbolic checker frontier, 13 November 2026 UTC

This is source/proof analysis, not a new accepted theorem or compiler request.
It follows root's direction to stop adding external finite-bound schemata.

The original predicate is fixed by GorbowPublishedDCBDefinitions:
Pr_D(sigma) = applyProv pF c (binaryCodeTerm 0 #rho #sigma), with TWO
existentials for fuel/certificate. Its named call uses checkerTag pF and
inputs [encode(c), fuel, 0, formulaCode, certificate]. The actual sigma/tau
sentences are fixed outside the object formula. They may contain arbitrary
full-language truth/knowledge syntax. No replacement proof predicate is needed.

Write Q(s,f,z) for the literal source formula
  call checkerTag [#encode(c), s, #0, #f, z] = #1.
This shorthand retains arbitrary source TERMS s,z, not their standard values.
After the already paid literal implication-code equalities are used, the
precise missing MP conclusion is an ordinary S derivation of the closure

  forall s,t,i,a,
    Q(s, #(rho -> (sigma -> tau)), i) ->
    Q(t, #(rho -> sigma), a) ->
    exists u,o, Q(u, #(rho -> tau), o).

ALL six displayed input/output numbers here are object-language variables
or existential witnesses; there is no external fuel/certificate bound.
Existing HBQuantifierSupportProof provides ordinary existential monotonicity,
elimination and vacuity. Those logical consumers can discharge the two source
Pr_D antecedents once this SAME-checker internal closure is genuinely proved.
The installed source prD term, not a fresh Pr predicate, remains the endpoint.

The external algorithm underlying this formula is completely explicit:
HBCertificateMPProof.conditionalMP uses TWO original mpCertificate calls and
the singleton original logical S-scheme certificate, with rho retained in
every formula code. conditionalMPMaxFuel feeds the inputs into q at max s t.
But its proof calls external certificateFuelMonotonicity and
numericModusPonens. Neither invocation is an internal S derivation.

The exact induction invariant for numeric MP is visible in
GorbowTheoryCertificateOperationsProof:

  1. line_suffix preserves an accepted original line when a tail is appended
     to the history. Rules2/3 use their actual successful reference bounds
     and getElem?_append_left. Canonical source-axiom rule4 has its own branch.
  2. successfulHistoryExtension proves, by induction over the second proof's
     line list, that run ax h ls=some out implies
     run ax (h++tail) ls=some (out++tail).
  3. run_shape/verify_info track exact reversed conclusion histories, their
     heads, and the equality of history length with proof length.
  4. mp_raw appends the implication proof, the antecedent proof, then ONE
     mpLine. Its literal references are antecedent.length and 0 in the
     combined history ah++ih. These exact offsets must survive arithmetization.
  5. numeric_info and calibration discharge the real sorted formula decoder
     and faithful certificate decoder; malformed inputs take the false branch.

For an internal proof, histories, line lists, successful Option results and
list lengths in these invariants must be represented by THEIR CURRENT numeric
codecs. The induction variable is the coded proof list length (or a justified
numeric coding descent), with history/tail/code/fuel parameters retained in
the induction formula. It is not induction over a family of standard finite
certificate bounds. The primitive PR functions for list append/lookup/length,
certificate decoding, sorted decoding, rule checks and run are already known
externally. Their named AST equations must be linked to these internal
invariants by ordinary source derivations, including the decoder inversion and
reference-bound facts. No such internal code/history invariant is currently
exported by the inspected suppliers.

There is a separate fuel obligation. axiomCheck(c,s)(raw) is defined by the
bounded ordinary evaluator evaln(s,c,encode(raw))=some 1, and the current proof
of certificateFuelMonotonicity invokes Lean's evaln_mono. Internal MP needs
the corresponding ordinary source arithmetic evaluator-monotonicity proof
with s,t raw/program parameters retained, then an induction over checked
lines. Choosing an external max fuel, or knowing a finite S stage externally,
does not discharge that internal evaluator statement.

The exact missing quotation conclusion similarly is

  forall s,i,
    Q(s, #(rho -> sigma), i) ->
    exists u,o, Q(u, #(rho -> Pr_D(sigma)), o).

The installed producer suppliers solve important but DIFFERENT tasks.
EffectiveNumeral.Proof.allNodeCertificates performs structural induction on
the FIXED PR AST and returns HasCertificates. HasCertificates is DEFINED as
an external existential Primrec generator plus a forall over standard inputs.
Its recursionFamily grows the generated proof by Nat.rec and proves accepted
output using a LEAN induction on the external counter and external numeric MP.
InstalledProducerProof.programProducer then uses allPrimitiveFunctions to
obtain an actual Program6 whose evaluation is extensionally this generator.
InstalledProducerRegistryProof correctly installs that program BEFORE c/rho
are selected. StageProof.generatedAtOneStage supplies one global S fuel and
actual CLOSED computation equations for each standard input.

To make this an unbounded internal quotation proof, the structural compiler
needs to return a syntax-specified producer AST together with an ordinary
source proof of its symbolic checker invariant. The recursion case must apply
PA(L)'s induction constructor to THAT invariant, with all other inputs free.
The generated formula code must use the original numeric numeral/code
constructors and exact source tag; under the Q=1 antecedent it must be
rewritten to the code of the literal successful checker equation. The current
existential AST evaluation equality from allPrimitiveFunctions is external;
it is not by itself an S theorem linking an arbitrary installed producer call
to that symbolic code/certificate recurrence. The same issue applies to the
fixed universal checker q selected by fixedUniversalProgram.

Thus the next genuinely unpaid bridge is a syntax-preserving, internally
verified recurrence/representation package for these SPECIFIC source checker
and producer algorithms, including internal list/history extension and
evaln-fuel monotonicity. This is more precise than requesting another numeral
correctness theorem or claiming generic Primrec existence internalizes an
external proof. One may choose the needed explicit implementation in the
EXISTENTIAL SelectedCertifiedPresentation construction while preserving the
same numeric checker relation and original Pr_D formula; one must not insert
the symbolic invariants as new source axioms or oracle premises.

Inspected files: GorbowTheoryCertificateOperationsProof;
GorbowTheoryNumericCertificate; GorbowTheoryChecker;
GorbowEnumeratedProvabilityDefinitions; GorbowEnumeratedCertificateFuelProof;
CertifiedSourceProvabilityCompletion/HBCertificateMPProof;
EffectiveNumeralDefinitions, EffectiveNumeralFamilyProof,
EffectiveNumeralRecursionAssemblyProof, EffectiveNumeralRecursionProof,
EffectiveNumeralProof, EffectiveNumeralTagTargets;
InstalledProducerDefinitions, InstalledProducerRegistryProof,
InstalledProducerStageProof and InstalledProducerProof.

Status: the specific symbolic source invariants above remain UNPROVED.
REQUEST-01's checked CK component, REQUEST-02's queued additional-axiom rule,
and REQUEST-03's queued bounded MP rule do not establish them. In particular
no omega-rule inference from all external bounds is available. Full source
HB2/HB3, the exact three local HB instances, SourceCollapse, the original
common-belief corollary and the full selector classification stay pending.
