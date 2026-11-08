# Original application-step guards: frozen semantic scope

Baseline: `29798a32f6f602268e6000efe05987490e98b30a`.
The exact definition, target and Preflight source hashes are recorded in
`FROZEN-SPECIFICATION.json`, before any proof authorship.

## Source correspondence

Paper06 `paper.tex`, SHA-256
`bdafe9f113ec4e3ffc390a5a744ae6337f197ab9a69ddcecd006d5dc08c4a66e`,
lines 537–549 describes the original finite-type auxiliary system and explicitly
allows function-side reduction in auxiliary application. It explicitly excludes
argument-side monotonicity. Lines 551–556 introduce the primary quotient,
least-code representatives, and arithmetic edge/path relations. The present
targets supply only an original step-checker semantic prerequisite to that
arithmetic construction, not an internal ID1 rule or the lemma at lines 558–560.

## Exact targets

1. `ActualPathDecoderLift` preserves `decodePath` on every natural suffix after
   prefixing the original encoded position 2. Invalid position entries remain
   invalid. The already proved total natural-list decoder does not imply that
   every list of naturals is a valid list of positions.
2. `ActualCertificateDecoderLift` says the unchanged `liftStep` commutes with
   `decodeStepCertificate` through `Option.map liftCertificate`, on every Nat.
   No premise of successful certificate decoding is allowed.
3. `ActualRawCodeIdentity` is equality of `stepCodeTest` on arbitrary raw Code
   terms, original StepCertificate data, and function-side application. It
   preserves focus context/type, replacement decoder, root selector, and literal
   replacement equality. It adds no well-formedness hypothesis on raw Code.
4. `ActualSourceUniverseDecomposition` states the exact source application guard:
   result type in S, function in the original universe, and argument in the
   original universe. No subtype-closure hypothesis hides these conditions.
5. `ActualTypedNumericIdentity` is equality of the original `numericStepTest`
   for every natural certificate, at original typed packed endpoints. Source
   function and argument are in the universe and the result type is in S.
   The target function is typed, with no added universe premise. False values,
   including malformed-certificate rejection, must be preserved.
6. `ActualRawEndpointIdentity` uses arbitrary natural source, target and argument
   codes with their exact original typed decoder guards. Source and argument use
   `decodeUniverse`; target uses `decodePackedNumber`, not `decodeUniverse`.
   The result-type guard is explicit. The output uses original `rawApplication`.
7. `ActualSubtypeClosedNumericIdentity` supplies the result-type guard from the
   original subtype-closed window and source function membership, while retaining
   every certificate and the same unfiltered typed target.

The specs import and refer directly to existing original definitions. They
introduce no new checker, alternative calculus, or semantic reflection rule.

## Existing suppliers and remaining boundary

`ApplicationCertificateLiftProof.actualTypedLift` already gives a typed Bool
equality for a structured StepCertificate. Its numeric consumer
`actualOriginalNumericLift` gives only successful-acceptance preservation.
This family closes the all-Nat semantic equality gap, not the internal proof gap.
The original raw Code `focusCode_cons` and `replaceCode_app` equations expose
the structural identity without adding target universe restrictions.

The existing `InternalQuotientEdgeChecker` step and representative programs
are selected by opaque primitive-function representation. Semantic equality
does not itself create a derivation for those programs. Internal step
acceptance, representative congruence, CertifiedApplicationLift, joint-context
and outer pathValue assembly, and the all-term ID1 endpoint remain separate.

## Verification state

The original three specification files were frozen before proof authorship.
After approved runtime restoration and a coordinator slot grant, the frozen
Preflight passed. All seven proof declarations and exact aliases subsequently
passed under the unchanged bounded profile, with actual axiom closure restricted
to propext, Classical.choice and Quot.sound. The focused closure contains 656
source-matched local modules. The first failed candidate is retained locally;
the accepted candidate changes only explicit instantiation of proof lemmas.

All frozen target and original-source hashes are unchanged. There is no new
axiom, admission, alternative checker, native_decide, or internal reflection.
The global register is unchanged. No Git operation or publication was performed
by this lane. This check does not claim a full-root or remote-CI build.
