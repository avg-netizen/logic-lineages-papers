# Independent internal-type statement/source review

Client date: 2026-11-22 (America/Chicago). Reviewed base:
`9a8fd8f8ffd9c1ab27b91096dc1e52aa196bb413`.

## Verdict and acceptance scope

**No material mismatch was found between the two frozen target modules, their
source map, and the existing object calculus.** The packet supplies internal
finite-list membership elimination/introduction, finite transfer to graphs of
the unchanged supplied programs, and grammar-codomain inversion under an
explicit finite numerical closure condition. These are substantive supporting
components; they do not close a numbered Paper 16 theorem.

The source map states the retained premises accurately. In particular, it does
not infer literal window membership from an arbitrary installed scalar or
window graph; infer closure from a bare `Settings`; replace the actual all-type
checker by a finite refitted checker; or infer an arbitrary-open program law
solely from unrestricted numerical calibration. The finite-checker obstruction
recorded in #1475 remains unchanged.

## Frozen propositions

The following references abbreviate files in
`LogicLineages/PersistentMarking/`:

- `MembershipTargets` means
  `NumberedWindowInternalLiteralTypeMembershipTargets.lean`.
- `CodomainTargets` means
  `NumberedWindowInternalGrammarCodomainTargets.lean`.

| Target | Exact assumptions and conclusion | Acceptance scope |
|---|---|---|
| `ExactLiteralTypeMembership`, MembershipTargets:38–43 | For every positive body, variable type, formula context, finite numeric list and open candidate, derive the conjunction of the two implications between literal membership and the finite disjunction of candidate-to-numeral equalities. | Unconditional internal characterization of this literal list. It is not an assumption that the candidate belongs to it. |
| `ExactFiniteProgramGuardTransfer`, MembershipTargets:48–53 | If the supplied `Program 1` evaluates to one at every listed numeral, a derivation of literal membership yields a derivation of its original unit graph at the same open candidate. | Finite transfer for the unchanged program, conditional on both the stated finite numerical evidence and actual internal membership. |
| `ExactFiniteProgramImageTransfer`, MembershipTargets:57–63 | If each listed input's numerical program value belongs to an output list, input membership and the actual open program graph yield literal output membership. | Requires the actual graph relating the candidate to the proposed result; it does not identify arbitrary results or assume an open evaluation oracle. |
| `ExactFiniteActualTypeGuard`, MembershipTargets:67–72 | `ActualTypeGuard TV`, validity of every listed code, and internal candidate membership yield the original supplied `TV` graph with output one. | A valid finite-list instance of the actual all-type checker. `TV` is neither replaced nor assumed to have an internal unfolding law. |
| `ExactFiniteWindowRefitGuard`, MembershipTargets:78–83 | `GrammarTypeInclusion s`, `TypeGuardCalibrated s T`, validity of every member of `s.window.1`, and internal membership in that literal window list yield the original `refitGuard s T` unit graph. | Keeps the actual supplied window guard and the existing refit program. It does not establish a refitted `InstalledTupleAt` or global `ActualTypeGuard` for that refit. |
| `ExactOpenFiniteGrammarCodomain`, CodomainTargets:29–33 | Under `FiniteCodomainClosure s.types`, derive the internal implication from literal grammar membership of `rawCons dom cod` to literal grammar membership of `cod`, for all open fields and contexts. | An original-calculus open implication obtained from the explicit finite closure property. |
| `ExactFiniteGrammarCodomainInversion`, CodomainTargets:37–39 | Under the same finite closure, return the existing `GrammarCodomainInversion body s` for every positive body. | Discharges the grammar-membership component of the earlier component interface, while preserving its finite-closure premise. |

The variable `Γ` in these propositions is a list of object-language formula
assumptions. It is not a numeric address context, a source typing context, or
the finite port context in the manuscript. Universal quantification over this
`Γ` is the usual stability of a derivation rule under assumptions. It does not
make membership, validity, or program acceptance unconditional: the guard and
image results still require derivations of their stated input formulas.

## Literal membership and the two encodings

`literalMembership codes candidate` is definitionally
`memberGraph (numeral (Encodable.encode codes)) candidate`
(MembershipTargets:25–28). The existing `memberGraph` is
`programGraph scratchMember 1 [code,candidate]`
(`NumberedWindowInternalSparseScratchMembershipTargets.lean:25–26`). The
existing `scratchMember` is the original standard list recursion whose nil
branch returns zero and whose cons branch tests the actual head, then uses the
same tail's membership result
(`NumberedWindowInternalSparseScratchMembershipDefinitions.lean:14–29`).

The source map correctly distinguishes this standard list encoding from the
sparse polynomial encoding used for a type arrow. The finite list contains
natural numbers that may themselves be sparse type codes; its enclosing list
is still encoded by the standard `Encodable` list codec. Nothing in the new
target uses `rawCons` to encode the enclosing scratch list.

`literalChoices` preserves the actual list structure (MembershipTargets:30–34).
An empty list yields falsity. A cons adds exactly one equality disjunct, and
duplicates remain duplicate disjuncts. Thus zero is accepted only when zero
occurs in the list; no default zero witness or extra candidate is introduced.
The equivalence applies to any finite numeric list, including malformed type
codes. Type validity is deliberately a separate premise in the type-guard
instances.

## Numerical transfer stays inside the original calculus

The relevant judgment is the unchanged
`ID1Completion.InternalCalculus.Derivation`. Its definition has explicit
logical, equality and arithmetic rules, plus closure and leastness for one
fixed positive body; it has no rule accepting arbitrary semantic truth or
program correctness
(`LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/InternalCalculusDefinitions.lean:76–116`).

The accepted numeral interface likewise refers to the supplied program's
actual graph: `NumberedWindowNumeralGraphTargets.lean:15–20` states that, for
each actual numeral tuple, there is a derivation of
`programGraph p (numeral (evaluate p v)) (inputs v)`. The new frozen statements
use only finitely many such numerical cases, selected by an internally proved
finite equality disjunction. Their hypotheses do not introduce a reflection
principle for an unrestricted open input.

The image-transfer target retains both membership and the supplied program's
graph in the same `body` and `Γ` (MembershipTargets:60–63). This matters: the
finite numerical value supplies a concrete output numeral, while the actual
open graph identifies the result under the object's existing equality and
graph laws. The target is not simply a statement about externally interpreted
numeric functions.

## Actual TV and refit hypotheses

`ActualTypeGuard TV` is calibration on **every** natural input:
`evaluate TV [n] = (typeBit n).toNat`
(`NumberedWindowInternalSparseAddressPositiveCalibrationTargets.lean:20–21`).
The actual-type instance preserves this exact hypothesis and adds that each
listed code has `typeBit = true`. Its output is acceptance by that same `TV`
at an arbitrary open candidate already proved to belong to the literal list.
It does not prove `ArrowCodomainInversion body TV`.

The supplied `T` has a different role. `TypeGuardCalibrated s T` means
`run T ty = (typeGuard s ty).toNat`
(`NumberedWindowInternalAuxWindowStepTargets.lean:21–22`), where
`typeGuard s ty = typeBit ty && s.window.1.contains ty`
(`NumberedWindowInternalAuxWindowMemoTargets.lean:21`). The refit program is
literally `conjunction T (grammarTypeAt s)`, and `grammarTypeAt s` calls the
original scratch-membership program on `Encodable.encode s.types`
(`NumberedWindowInternalSettingsGrammarGuardDefinitions.lean:22–31`).

`GrammarTypeInclusion s` is exactly inclusion of the same settings' window
list in the same settings' grammar list
(`NumberedWindowInternalSettingsGrammarGuardNumericTargets.lean:13–15`).
Together with the validity premise and literal window membership, these
hypotheses suffice for the stated finite refit result. They do not say that
all valid types are windowed, that acceptance of a general source address
supplies this membership, or that `T` and `TV` are interchangeable.

Consequently there is no conflict with #1475. Its obstruction concerns using
the finite refitted checker in a slot requiring `ActualTypeGuard` on all
natural inputs. The new result proves a refit graph only for a candidate
already constrained to a specified finite window. It does not change the
global checker or that slot's obligations.

## Grammar codomains, finite closure and the manuscript

`FiniteCodomainClosure codes` is exactly
`∀ code ∈ codes, evaluate cellTail [code] ∈ codes`
(CodomainTargets:20–24). It covers **every** listed code, not just codes already
known to be valid arrows. This is an explicitly stronger finite condition than
arrow-only codomain closure on an arbitrary list. The source map discloses
that distinction at lines 48–55. It is not a hidden assertion about every
`Settings` value.

The projected program is the original
`cellTail := atPredecessor rightCandidate`
(`NumberedWindowInternalSparseFieldCell.lean:12–21`). The open constructor is
the original `rawCons dom cod := suc (pairTerm dom cod)`
(`NumberedWindowInternalSparsePathEnvelopeTargets.lean:23–25`), with
`pairTerm x y = (x+y)*(x+y)+x`
(`NumberedWindowInternalSparsePair.lean:18–20`). This is the same arrow
constructor as `arrow dom cod = pair dom cod + 1`
(`NumberedWindowAnnotationAlgorithm.lean:13`). The existing `canonicalCell`
interface proves the actual cell graph for arbitrary open fields
(`NumberedWindowInternalSparsePathEnvelopeOpenCellProof.lean:31–33`). Thus the
new statement projects the literal codomain of the original encoded arrow.

The output `GrammarCodomainInversion body s` is the existing rule at
`NumberedWindowInternalCoverMeasuredApplicationTypeCalibrationTargets.lean:34–44`:
membership of that original `rawCons` in the literal `s.types` list yields
membership of its codomain. It is not an independent new definition that
quietly weakens the earlier interface.

Paper 16 uses a finite subtype-closed type family: literal support is closed
under type subexpressions (`sections/foundations.tex:87–100`), and the decision
construction chooses `K` as the subtype closure of the input types
(`sections/decision.tex:9–13`). The finite-closure proof explicitly invokes
domain, suffix and codomain subtypes (`sections/decision.tex:22–38`). These
facts motivate the supporting membership/codomain construction.

They do not make `FiniteCodomainClosure s.types` automatic for arbitrary
settings. `Settings` contains only a window, a numeric type list and head
pairs (`NumberedWindowScalarAlgorithm.lean:15–19`), with no closure field. The
original source specialization has `(fixed S K).types = K.map encodeTy`
(`NumberedWindowArithmeticScalarTargets.lean:12–13`). An integration that
removes the new closure premise must supply the exact numerical closure for
that actual list, including the total program's behavior on base codes; it
cannot cite only the existence of a finite list or the bare settings type.
The present target does not claim to supply that specialization.

Even after this grammar component is available, the earlier refit inversion
assembly still separately requires `ArrowCodomainInversion body T`
(`NumberedWindowInternalCoverMeasuredApplicationTypeCalibrationTargets.lean:46–51`).
The actual all-type checker has its own inversion obligation. No source
application guard, complete source translation, internal accessibility theorem,
or ordinal-bound supplier is discharged by these two packets alone.

## Frozen pins and native-status boundary

The three current hashes match the preproof freeze recorded in the internal
types lane at `2026-11-23 05:20:05 UTC`:

| Reviewed file | SHA-256 |
|---|---|
| `NumberedWindowInternalLiteralTypeMembershipTargets.lean` | `fb41b63bb1d132b66979bce426eb4f3509f38df59fab4dbf71b3ca36ffd27611` |
| `NumberedWindowInternalGrammarCodomainTargets.lean` | `ba40bbdde6d2225f71cf7c81ff39b9f2d61cf9551f96f16c9c3fe83c121ff1a7` |
| `internal-types/INTERNAL-TYPES-SOURCE-MAP.md` | `41cc8863e783f6feb8f5a31212c4ad63511ce6325fb6d5418952197eff9dba95` |
| `InternalCalculusDefinitions.lean` | `557cb2999f699e7959a91fd9f52b3207ebaa5ee3e2b51dd103b64013af71d85d` |
| Paper 16 `sections/decision.tex` | `bbf73326e21a6e71984bd46e8c86696013c65ac1875a113a48786db996880af9` |
| Paper 16 `sections/foundations.tex` | `a1f3a425ac6b92ecd4beceab77f271a1b9af97343360a9eee304beb23c7537e0` |

The root reports that native gate09,
`build-reports/1795412014343677355-11.json`, passed all five membership aliases
and both grammar aliases with standard axioms only. Native validity and its
evidence packaging remain the root's gate; this review is an independent
statement/source assessment, not a duplicate proof-body or compiler review.
No existing frozen file, calculus definition, manuscript or register was
modified for this review.
