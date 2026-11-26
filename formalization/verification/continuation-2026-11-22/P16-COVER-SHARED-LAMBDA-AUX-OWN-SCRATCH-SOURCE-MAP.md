# Paper 16: literal lambda and auxiliary own-scratch on one shared V and measure

Status: frozen source, native gates pending. Both roots use exactly
`sharedCover V TV M := selectedCover (sharedSyntax V TV) (sharedMeasure M)`
and the original physical scratch output of this program, not an older
lambda or auxiliary scratch program. Queue independent lambda final and
auxiliary chain: `exact_OpenCoverChildOwnScopeCases`, `fromActualBounds`
and `boundsRename`, `fromSharedMeasured`, `exact_OpenCoverSharedAuxOwnScratch`.
Lambda final alias `exact_OpenCoverSharedLambdaOwnScratch`.

Lambda consumes the actual shared parent validity and measurement;
checked shared roots recover actual child V and M, the original child
standard pair and the actual parent pair at its supplied code. Observe the
original selected grammar at that measured child depth and numeral width
and specialize the one local typed-body IH to the actual term list. The
existing generic exact LambdaMeasuredScratch theorem installs the body
scope and root as appropriate and identifies the given parent scratch.
The actual W body observation and typed context are supplied as a premise;
no lambda parent W observation or lexical/protected W inversion is claimed.

Auxiliary uses the actual shared V parent and the genuine strict auxiliary
W parent (independent TV and TW). The checked roots give both actual V
children and same-context typed W children. The actual shared M parent gives
one correlated pair per child and one correlated parent-bound report tied
to its same literal chosen combine output and type-ordered children. At
both real measured scopes, original selected grammar totality provides
the physical observations. Install each as the same shared-cover scratch
on that child and specialize only that child’s original local type/scratch
IH. Keep two bona fide K members and exact supplied parent scratch.
Transport and eliminate the actual width witness from the shared
measurement bound report once; feed the resulting original same code,
same pair, four weak bounds and actual child occurrences directly to #975.
There is no dependence on an assumed equality of different selected
programs, V or M reflection of old guards, arbitrary additional constructors,
or protected ambient closure.

## Frozen sources
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSharedOwnScratchTargets.lean`: `4ece283b7611f0815c08a6dc0fcf3997c664e2ed55487427476c0f8ff621bf60`, 1167 local modules.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSharedLambdaOwnScratchProof.lean`: `a4653459a212a02d340f431669ef07e2a12dcba36f2485cc483e595b3c4b49b3`, 1516 local modules.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverChildOwnScopeProof.lean`: `64db0bc179520687ecdc028491d69354e7176bac2961dfef493072eb885f2349`, 1438 local modules.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverAuxOwnBoundsAssemblyProof.lean`: `9f57d49856d06a71951c17b90038aa545812bc4472394c93896895dd78eba812`, 1489 local modules.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSharedAuxOwnScopesProof.lean`: `ffafdcaf369c932636113061d2eb0c47b3e902b2ec662a1036a6ea20e046440a`, 1495 local modules.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSharedAuxOwnScratchProof.lean`: `f3687748458b4385d067fb42515caf2961ed2fef63d22b4f5c77e803a2f8ca37`, 1530 local modules.
No explicit Hydra or Linarith in these static local import closures.

## Principal exact origin pins
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSharedLambdaSyntaxProof.lean`: `5b62f0f3b2cc09864ea989fb4907f2e8cbfb66ee79b826d55dece08738fda144`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSharedAuxSyntaxProof.lean`: `7c04e4625794ea9c9f646c8af6523d84341bd987f7c1f7235468a88d91996953`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSharedLambdaMeasureProof.lean`: `f1c2ea9818cb57529a919992fd5b6dab20d7f0f3fcb5876fac9f44e2ecacf5bb`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSharedAuxMeasureProof.lean`: `62beb8006fdce2832c13f400ff92582958cf5a4e3b56dac234096a0f960a7730`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalStrictAuxWindowParentProof.lean`: `eab706f734ba54165112f3e0b93ccac58c49ab26f8b92751fa4d9d25ae269e25`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSelectedGrammarLambdaOwnScratchProof.lean`: `3fd45e718b72e5bb5428fce0bcc70c0ac0fd65f59c589f5c4955d1f5bcd08bec`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSelectedGrammarAuxScratchMembershipProof.lean`: `662c2cf7b678c3c20eb0ec6774c589e0c00bbb913c934774502a9e068e5d93c5`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSelectedGrammarOptionOpenProof.lean`: `76f994c9245631a2087dc74d05987ca0636aae5741a61b9d472d70c2f0975258`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSelectedGrammarWidthObservationProof.lean`: `042ae786db3d73c99012d1bb9c80d869c9cde86bcd6cc8f37e5ef21057f2c5b7`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverLambdaDerivedOwnInputSyntaxProof.lean`: `df8492ba533e4c6dd0a4dc7c1c039d21b337011700b43ede2f2e3334ea9097c8`.
