# Paper 16 accessibility target revision

Paper 16 fixes a finite subtype-closed source universe and defines the
computability formula by recursion on its types. The milestone's source list
`K` has elements of `PersistentMarking.Ty`. The object-language functions
`typedAt` and `formula` both take `OrdinalComparison.Source.Ty`. The revised
target applies the existing `formulaType` at its two typing call sites and
one computability call site. The selected original window already uses this
conversion elementwise in `sourceWindow K`. [Manuscript, arithmetic accessibility](../../../../16-persistent-marking-termination-ordering/sections/ordinals.tex) ·
[Conversion](../../../LogicLineages/NativeModule/PersistentMarking/NumberedWindowOriginalComputabilityFormulaTargets.lean) ·
[Revised target](../../../LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneTargetsV2.lean)

The revision is in module
`LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneTargetsV2`
and namespace
`LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneTargetsV2`.
Its uniform projection supplies the ordinal interface with the installed
scalar, `jRaw` applied to that scalar, the installed path, and `dCore` over
that scalar, path, and the original permutation, at the original derivation's
context. [Uniform projection](../../../LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneUniformProjectionV2.lean)

## Downstream import rebasing

All names in the table have the prefix `Paper16AccessibilityMilestone`.
Each rebased module uses a `V2` suffix for its short name and declaration
namespace and takes its milestone references from the indicated dependencies.
Module imports use the
`LogicLineages.NativeModule.PersistentMarking` prefix. Declaration names use
the `LogicLineages.PersistentMarking` prefix.

| Downstream V2 module | Direct V2 import | Namespace references to rebase |
| --- | --- | --- |
| `InstalledPacketV2` | `TargetsV2` | `TargetsV2` |
| `WindowSelectionV2` | `InstalledPacketV2` | `InstalledPacketV2`, `TargetsV2` |
| `JoinedWindowSelectionV2` | `WindowSelectionV2` | `InstalledPacketV2` |
| `InstalledLambdaWindowV2` | `JoinedWindowSelectionV2` | `InstalledPacketV2`, `JoinedWindowSelectionV2`, `TargetsV2` |

`InstalledWindow` is a structure in each version's target namespace. A V2
consumer obtains its witness from `InstalledPacketV2.installedOfPacket`.
The validity, seed coverage, fixed-settings, and shift-lambda suppliers live
in the shared source modules or their existing native ports.

The independent `DirectWindowSelectionV2` root uses the target, original
window validity, and direct carrier packet imports. It builds the same
`InstalledWindow` from `packet.physical`. The source planner reports 3,078
local modules for this root and 3,907 for the selection root through the
joined packet. [Isolated direct selection](../../../LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneDirectWindowSelectionV2.lean)

The revised target compiled in receipt `1795732330232907973-10`. The
uniform projection and all-terms assembly both passed in receipt
`1795732701414573728-10`. The remaining downstream modules await their
serialized Lean checks.

## Original window correspondence

The manuscript fixes a subtype-closed type universe, represents all finite
contexts and fresh extensions in that universe, and uses least representatives
of the finite quotient. The following statements supply the corresponding
numeric interfaces at the original `fixed S K`.
[Manuscript, one finite arithmetic universe and clauses (A) and (T)](../../../../16-persistent-marking-termination-ordering/sections/ordinals.tex)

- `ExactClassApplicationGraph` calibrates the arithmetic graph against
  `appClass`. Successful argument and result addresses represent classes at
  the original finite context, with the exact arrow domain and codomain.
  [Application graph target](../../../LogicLineages/NativeModule/PersistentMarking/NumberedWindowApplicationGraphTargets.lean)
- `ExactFreshArrowProbe` selects a name above the numeral bound of the
  decoded canonical term and supplies its free-variable class at the same
  finite context and exact domain. `FreshProbeApplication` applies the
  original numerical graph and requires a typed result at the codomain.
  [Free-address target](../../../LogicLineages/NativeModule/PersistentMarking/NumberedWindowFreeAddressTargets.lean) ·
  [Typed probe target](../../../LogicLineages/NativeModule/PersistentMarking/NumberedWindowTypedProbeTargets.lean)
- `ExactOriginalValidWindow` joins type support for all successful raw
  type tests, closure under arrow codomains, and numerical probe/application
  totality on all typed arrow inputs. The selected list is literally
  `K.map formulaType`. The numerical proof supplies premises for the
  separate derivability and computability arguments in the paper.
  [Window interface](../../../LogicLineages/PersistentMarking/NumberedWindowInternalFreshProbeDispatchWindowTargets.lean) ·
  [Original window target](../../../LogicLineages/NativeModule/PersistentMarking/NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets.lean)

The first native port, `NumberedWindowAddressApplicationTargets`, compiled
with its original three declarations in receipt `1795732198303922752-10`.
The corresponding proof gate passed in receipt `1795732212191449175-10`.
The axiom reports for `exact_DecodedApplication` and `exact_ClassApplication`
list `propext`, `Classical.choice`, and `Quot.sound`.

The full original-window gate passed in receipt `1795732271110127724-10`.
Its 296 local rows include 231 cache hits. The axiom reports for
`exact_OriginalTypeSupport`, `exact_OriginalWindowChild`, and
`exact_OriginalValidWindow` use only the same three standard axioms.

## V2 statement correspondence

- The source list `K` still determines the branch types in
  `CarrierTypingCases` and the admitted types in `TypedCarrierComputability`.
  `formulaType` carries ground and arrow constructors to their matching
  object-language constructors. The checked `exact_FormulaTypeCoding`
  equates the resulting probe code with the original numerical type code.
  The existing probe reading `ExactProbeTypeCoding` uses that probe code for
  `typedAt`. Thus the formula and the type guard refer to the same source type.
  [Formula coding check](../../../LogicLineages/NativeModule/PersistentMarking/NumberedWindowOriginalProbeTotalChecks.lean) ·
  [Probe reading check](../../../LogicLineages/PersistentMarking/NumberedWindowProbeReadingChecks.lean)
- `InstalledWindow` refers to one original signature, one closed source
  list when selected, and one set of installed programs. The raw transition,
  least representative, typed probe, and application fields stay tied to
  this presentation in the four `ApplicationArithmetic` fields. The
  backward and forward obligations correspond to the use of function-side
  closure in downward closure and in the inference from computability to
  `I`. [Revised target](../../../LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneTargetsV2.lean) ·
  [Manuscript, computability facts](../../../../16-persistent-marking-termination-ordering/sections/ordinals.tex)
- `AllTerms` asks for an internal derivation of the quantified scalar
  sentence on the same four programs. The presentation wrapper projects to
  the whole address and passes the supplied transition certificate to the
  original check. Its outer context argument has no effect on the unary
  address check, so a fixed outer numeral does not restrict the set of
  encoded finite contexts represented by the addresses.
  [Checker coordinates](../../../LogicLineages/PersistentMarking/NumberedWindowCheckerCoordinates.lean) ·
  [Tagged and all-terms semantics](../../../LogicLineages/PersistentMarking/NumberedWindowInternalPresentationChecks.lean)
- `exact_SelectInstalledWindows` gives the direct installed packet for
  every subtype-closed `K`, with witness list `sourceWindow K` and the
  same signature entries, settings, scalar, guards, raw transition, least
  program, application program, and probe inputs supplied by that packet.
  The stronger lambda selection builds its own witness at the same source
  list. Its explicit `A.raw` equation and joined rules refer to the same
  syntax program and depth-zero lambda instance. The type split,
  constructor computability, and open substitution preservation within
  the arithmetic accessibility proof remain separate obligations.
  [Direct selection](../../../LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneWindowSelectionV2.lean) ·
  [Lambda selection](../../../LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneInstalledLambdaWindowV2.lean)

## Checked conditional assembly

`exact_CloseAllTerms` introduces a universally quantified address and
discharges the scalar-carrier hypothesis after a case split over the
converted types in `K`. Within each branch, the typing derivation and the
typed computability derivation imply scalar membership using the same
presentation, application program, and probes. `exact_InstalledToUniform`
then projects the existing calibrated programs and context from any
`InstalledArithmeticAccessibility` witness. Both axiom reports list
`propext`, `Classical.choice`, and `Quot.sound`.
[All-terms assembly](../../../LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneAllTermsAssemblyV2.lean) ·
[Uniform projection](../../../LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneUniformProjectionV2.lean)

The all-terms assembly takes `CarrierTypingCases A c`,
`ApplicationArithmetic A c`, and `TypedCarrierComputability A c` as premises.
An installed packet and the numerical typing calibration supply the
presentation and numerical judgments. The manuscript's open typing and
computability steps must supply the corresponding derivations.

## Ground typing at the installed window

The selected checker `chosenH` dispatches over the actual probe list. Its
ground branch tests `priorTyped` together with the result-field equality
check. `exact_OriginalGroundTypedIntroduction` introduces that branch from
both original graph derivations. The original `priorTyped` witness comes
from primitive-recursive realization with an evaluation law.
[Ground introduction](../../../LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneGroundTypedIntroductionV2.lean) ·
[Original typed-program selection](../../../LogicLineages/PersistentMarking/NumberedWindowTypedProbeProgramChecks.lean)

`priorTypedOf` combines the installed unary scalar and the original
result-field equality test. Its draft calibration compares both programs
on every raw input. `retypeWindow` uses it as the prior checker and rebuilds
the typed-probe and alignment derivations. The ground assembly then uses
only the scalar carrier, the original result report at code zero, and ground
membership in `K` at that presentation. Its remaining branch premise is the
zero result report, and the arrow branches additionally need the actual
fresh/application and codomain reports used by `chosenH`. Lean checked the
ground introduction, prior-typing calibration, and both the prior-typing and
fresh-scalar reinstallations. The ground-branch assembly awaits its check.
[All-input calibration](../../../LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestonePriorTypedCalibrationV2.lean) ·
[Prior typing reinstallation](../../../LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneLiteralPriorTypedV2.lean) ·
[Retyped ground branch](../../../LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneRetypedGroundV2.lean)

The original joined packet has the finite scalar shape by definition.
`exact_InstalledLambdaWindowWithScalarAtOriginalWindow` retains this
equation. At `K = [Ty.ground]` the stored code list reduces to `[0]`.
`exact_RetypedGroundFromFiniteScalar` uses internal graph totality and
the literal singleton membership report to derive the zero result field.
`exact_OriginalGroundLambdaTypingWindow` applies the resulting
`CarrierTypingCases` to the same retyped joined packet and rebuilds the
joined rules that depend on `chosenH`.
[Joined packet with scalar equation](../../../LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneInstalledLambdaWindowV2.lean) ·
[Finite ground typing](../../../LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneGroundWindowTypingV2.lean) ·
[Retyped joined packet](../../../LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneRetypedJoinedWindowV2.lean)

`exact_OriginalArrowTypedIntroduction` constructs the actual nonzero
dispatch branches from the prior typing test, the arrow result code,
the selected fresh output, the option-application output, the guarded
application, and the recursive codomain type judgment. For a general
arrow window, the rest of the internal typing proof must derive those
fresh and application reports from the original scalar carrier and
type report, and establish the codomain typing on the same result.
[Arrow introduction](../../../LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneArrowTypedIntroductionV2.lean)

### Remaining arrow report suppliers

The original parsed tuple chooses `scalarProg` from
`exact_OriginalParsedFreshSelection` and `optionApplication` from the
binary part of `exact_ApplicationPrograms`. Both supply numerical
evaluation laws. The application reinstall retains these two physical
programs while setting `applicationGuard`. The V2 prior typing
reinstall retains both too.
[Original parsed tuple](../../../LogicLineages/PersistentMarking/NumberedWindowInternalFreshProbeParsedTypedSelectionChecks.lean) ·
[Application reinstall](../../../LogicLineages/PersistentMarking/NumberedWindowInternalSparseApplicationReinstallDefinitions.lean)

- The fresh report must use
  `programGraph (chosenA A.probes) (suc u) ![q]` at the selected address
  and body. Its positive branch first needs `selectedGuard A.probes.scalarProg`
  to return 1. That guard uses the actual `scalarProg` acceptance and
  both the address and arrow parser guards. Given the guard and original
  context, domain, and bound reports, `gatePreserves` introduces the
  selectors. The reverse direction of `exact_PackedFreeEmitterGraph`
  introduces the exact packed free address, and the successor branch
  introduces the original fresh report. The existing parsed-fresh
  theorem recovers coordinates from an accepted report. A proof on
  the retained selection must first derive open acceptance of its
  `scalarProg` from the installed carrier, along with the parser guards.
  A separate installation could use the installed scalar in
  `scalarProg` and rebuild the probe derivations before consuming the
  resulting `chosenA`.
  [Fresh selection](../../../LogicLineages/PersistentMarking/NumberedWindowInternalFreshProbeParsedEmitterNumericChecks.lean) ·
  [Fresh guard and selectors](../../../LogicLineages/PersistentMarking/NumberedWindowInternalFreshProbeParsedEmitterGuardProof.lean) ·
  [Packed emitter](../../../LogicLineages/PersistentMarking/NumberedWindowInternalFreshProbeEmitterObjectChecks.lean)
- The application report must pair
  `programGraph A.probes.optionApplication (suc v) ![q,u]`
  with `programGraph A.probes.applicationGuard (suc z) ![q,u,v]`
  for exactly the same `v`. The binary option program is selected by
  primitive-recursive realization. The reverse direction of
  `exact_OpenGuardedApplication` supplies the ternary acceptance from
  `applicationReport` on the same scalar and least programs. Application
  closure derives the result carrier from that acceptance. A proof for
  the retained selection must still obtain the existing binary option
  graph. A constructive installation could emit
  the successor-encoded result from the same guarded parsing and least
  output as the ternary frontend. It would need all-input option calibration
  and rebuilt probe proofs for that selected program. The existing
  `TypedProbeTotal` starts from `chosenH` acceptance and retains the
  fresh report, application guard, and codomain typing.
  [Binary option selection](../../../LogicLineages/PersistentMarking/NumberedWindowAddressApplicationProgramProof.lean) ·
  [Open guarded frontend](../../../LogicLineages/PersistentMarking/NumberedWindowInternalSparseApplicationFrontendOpenChecks.lean) ·
  [Application closure](../../../LogicLineages/PersistentMarking/NumberedWindowInternalLiteralEnrichedApplicationClosureProof.lean) ·
  [Typed-probe contract](../../../LogicLineages/PersistentMarking/NumberedWindowInternalProbeTargets.lean)

### Concrete replacements for the two selected programs

`reinstallFreshScalar` installs the same scalar that supplies the
presentation's carrier as the input to the original fresh selector.
`exact_ReinstalledFreshExists` derives the positive `chosenA` report
from that carrier, the literal finite scalar AST, and the actual `rawResult`
graph at the arrow type. It calls the original packed emitter on the
context, domain, and name supplied by its component graphs.
[Fresh scalar reinstallation](../../../LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneLiteralPriorTypedV2.lean) ·
[Fresh emitter introduction](../../../LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneFreshReportV2.lean) ·
[Fresh existence](../../../LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneInstalledFreshSelectionV2.lean)

`optionApplicationOf` emits the output address computed with the
installed least program when the original ternary guard accepts it.
Its all-input calibration and open successor report use the same
scalar, least call, and guard. `reinstallOptionApplication` changes
the binary option leaf and rebuilds the typed-probe and alignment
derivations. The open report applies to an accepted original guard on
the same result and the installed identity
`A.application = applicationCore A.least`. Both replacement chains passed
Lean with standard axioms. The remaining arrow step must establish the
fresh address's carrier and supply an accepted ternary application on that
address, then type the resulting codomain.
[Binary option program and calibration](../../../LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneOptionApplicationV2.lean) ·
[Open binary report](../../../LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneOptionApplicationOpenV2.lean) ·
[Binary option reinstallation](../../../LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneOptionReinstallV2.lean)

## Native gate handoff

Each short root below takes the module prefix
`LogicLineages.NativeModule.PersistentMarking.`

| Root | Result |
| --- | --- |
| `NumberedWindowAddressApplicationTargets` | Passed, receipt `1795732198303922752-10`. |
| `NumberedWindowAddressApplicationChecks` | Passed, receipt `1795732212191449175-10`. |
| `NumberedWindowInternalFreshProbeDispatchOriginalWindowChecks` | Passed, receipt `1795732271110127724-10`. |
| `Paper16AccessibilityMilestoneTargetsV2` | Passed within receipt `1795732330232907973-10`. |
| `Paper16AccessibilityMilestoneAllTermsAssemblyV2`, `Paper16AccessibilityMilestoneUniformProjectionV2` | Passed, receipt `1795732701414573728-10`. |
| `Paper16AccessibilityMilestoneDirectWindowSelectionV2` | Memory floor reached before the root, receipt `1795732739278525257-10`. |
| `Paper16AccessibilityMilestoneGroundTypedIntroductionV2` | Passed after the dependent `Fin.elim0` repair, receipt `1795736129561276514-10`. |
| `NumberedWindowOriginalFixedSeedCoverageProof`, `NumberedWindowOriginalFixedSettingsProof` | Independent pending roots for the original settings. |
| `Paper16AccessibilityMilestonePriorTypedCalibrationV2` | Passed after proving the negative Boolean comparison explicitly, receipt `1795736252400365946-10`. |
| `Paper16AccessibilityMilestoneLiteralPriorTypedV2` | Both prior-typing and fresh-scalar reinstallation passed with standard axioms, receipt `1795736252400365946-10`. |
| `Paper16AccessibilityMilestoneRetypedGroundV2`, `Paper16AccessibilityMilestoneGroundWindowTypingV2` | Pending ground branch chain. |
| `Paper16AccessibilityMilestoneInstalledLambdaWindowV2`, `Paper16AccessibilityMilestoneRetypedJoinedWindowV2` | Pending joined installation and same-witness singleton typing. |
| `Paper16AccessibilityMilestoneArrowTypedIntroductionV2` | Pending original-guard arrow introduction. |
| `Paper16AccessibilityMilestoneFreshReportV2`, `Paper16AccessibilityMilestoneOptionApplicationV2` | Fresh emitter introduction and binary option calibration passed with standard axioms within receipt `1795737463136335448-10`. |
| `Paper16AccessibilityMilestoneInstalledFreshSelectionV2` | Passed after renaming the reserved binder, with standard axioms in receipt `1795737917569319865-10`. |
| `Paper16AccessibilityMilestoneOptionApplicationOpenV2` | Open binary report passed after restoring the nonempty wrapper around the accepted guard proof, receipt `1795738027256006286-10`. |
| `Paper16AccessibilityMilestoneOptionReinstallV2` | Scoped binary option reinstallation, window reconstruction, and installed successor report passed with standard axioms, receipt `1795738027256006286-10`. |

The passed proof roots report only standard axioms. The direct selection
and conditional assembly are supporting contracts for
`lem:arithmetic-accessibility`. The general type split, application
matching, and constructor and structural computability remain outstanding.
