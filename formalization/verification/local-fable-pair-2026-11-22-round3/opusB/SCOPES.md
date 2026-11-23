# Opus B round-3 scopes (three lines each, for records)

## 1a. Guarded scalar norm — twin `LogicLineages.NativeModule.PersistentMarking.NumberedWindowGuardedNormProof`
- Says: for every address n and ordinal a, n is in stage a of the scalar accessibility operator (and of the tagged operator at the scalar tag) iff n is an admitted address that is accessible under the address-positive relation with rank ≤ a; the accessible rank is the least such stage (`exact_ActualScalarStageRank`, `exact_ActualScalarOrdinalNorm`, plus isolated starts at stage 0).
- Assumes: nothing (closed theorems); receipt `1795402033770287946-3275204`, axioms propext/Classical.choice/Quot.sound; one twin proof repair in the private law `scalarLaw` (round-3 manifest).
- Serves: `thm:upper` (step "the tagged I component has its standalone accessibility norm").

## 1b. Class rank = address rank = stage norm — twin `LogicLineages.NativeModule.PersistentMarking.NumberedWindowAddressClassRankProof`
- Says: for every closed window K, context Γ, type τ and quotient class q, the R_S-rank of q equals the address-positive rank of its canonical address (`exact_ActualAddressClassRankEquality`), and that rank is the least stage of the scalar and of the tagged ID operator containing the address (`exact_ActualClassStageNormAtAddress`).
- Assumes: nothing; receipt `1795402055383415156-3275283`, axioms propext/Classical.choice/Quot.sound; draft compiled unchanged.
- Serves: `thm:upper` (identifies rk_{R_S}(tr s) with the inductive norm to which the norm theorem applies).

## 2a. Literal native arithmetic realizers — twin `LogicLineages.NativeModule.PersistentMarking.NativeOrdinalArithmeticCompositionProof`
- Says: for every signature S, with the actual well-founded closed native strict order at ι, the literal closed native terms Z, s, add, mul, w (Cap), one, pow, fix and Next realize, for any semantic operations satisfying the ordinal and omega orbit equations, zero, successor, α+β, αβ, ω, 1, ω^α, f^ω(ζ+1) and the fix applied to pow (`exact_LiteralNativeArithmeticRealizes`).
- Assumes: nothing; receipt `1795402092285333664-3275481`, axioms propext/Classical.choice/Quot.sound; draft compiled unchanged (generic composition #518 + native beta/strict edges #512 + twin iteration #1446).
- Serves: `thm:height`, chain (R) — the explicit ordinal operations paragraph (ordinals.tex 500–530).

## 2b. Native arithmetic realization at the actual ordinal operations — new module `LogicLineages.NativeModule.PersistentMarking.NativeOrdinalArithmeticRealizationProof`
- Says: for every S there are a well-founded closed native strict order and countable-ordinal operations Z, s, add, mul satisfying the exact equations (Z = 0, s a = a+1, add = orbit of s with value a+b, mul = orbit of (·+a) from Z with value a·b) that the literal native zero, successor, addition and multiplication terms realize (`exact_NativeOrdinalArithmeticRealization`).
- Assumes: nothing; receipt `1795402162170917672-3276046`, axioms propext/Classical.choice/Quot.sound; proves the drafted proof-less target (frozen twin sha256 641f4a06…455d) from 2a and the module-system orbit theorems.
- Serves: `thm:height`, chain (R) (the realizers of +, ·, used in the tower terms).

## 3a. Pair programs, calibrated — twin `LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticPairProgramChecks`
- Says: there are Gorbow primitive-recursive programs computing the polynomial pairing (a+b)²+a and the complete optional pair decoder (canonical Encodable output, failure value off the image), and the registry calibration of pair and decode holds (`exact_ActualPairProgram`, `exact_ActualPairDecoderProgram`, `exact_PairAndDecodeCalibration`).
- Assumes: nothing; receipt `1795402204639313192-3276260`, axioms propext/(Classical.choice)/Quot.sound; draft unchanged.
- Serves: `lem:arithmetic-accessibility` (arithmetic coding of addresses; the combined legacy alias of #495 that hit the memory cap).

## 3b. Pair evaluation programs — twin `LogicLineages.NativeModule.PersistentMarking.NumberedWindowPairEvaluationChecks`
- Says: the same two statements (program for pair; program for the full optional decoder) over the `NumberedWindowArithmeticPair` definitions, obtained from the direct pair programs (`exact_ActualPairProgram`, `exact_ActualPairDecoderProgram`).
- Assumes: nothing; receipt `1795402232822083563-3276404`, axioms propext/Classical.choice/Quot.sound; draft unchanged.
- Serves: `lem:arithmetic-accessibility` (supporting arithmetic coding).

## 3c. Internal sparse pair decoding — twin `LogicLineages.NativeModule.PersistentMarking.NumberedWindowInternalSparseDecodeChecks`
- Says: the sparse candidate programs compute n−s², s−(n−s²) and the guard [n−s² ≤ s] with s = ⌊√n⌋; their chosen decoder equals the original optional decoder on every input; and inside the retained ID₁ object calculus, for arbitrary free terms, the pair-program graph is provably equivalent to the certified candidate outputs and a failing guard is provably equivalent to having no pair preimage (`exact_CandidateValues`, `exact_GuardValue`, `exact_AllInputDecoder`, `exact_OpenSuccess`, `exact_OpenFailure`).
- Assumes: nothing; receipt `1795402353896996749-3277001`, axioms propext/Classical.choice/Quot.sound; five one-line twin repairs (manifest).
- Serves: `lem:arithmetic-accessibility` (internal arithmetic for decoding addresses in the ID₁ derivation).

## 3d. Fresh-probe integration targets (definitions only) — twin `LogicLineages.NativeModule.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalIntegrationTargets`
- Says: only defines the two target propositions (selected / concrete original typed-probe totality: for the fixed source S,K and the original p, a programs there is one h whose typed-address calibration holds and with which every ID₁ derivation of an arrow-typed address yields the probe witnesses); no theorem.
- Assumes: n/a; receipt `1795402393988330714-3277234` (module compiles); no proof exists — proving it is the open internal fresh-variable totality.
- Serves: `lem:arithmetic-accessibility` (fresh computable variable at arrow types, gap-map item N3); a definitions-only record at most.

## 4. Confined rank ≤ tagged stage norm at tr q — new module `LogicLineages.NativeModule.PersistentMarking.NumberedWindowConfinedRankStageNormProof`
- Says: for every signature S and typed ordinary q : τ, the window K = TypeSupport.support q is closed and tr q = some Q with Q in that window (empty bound context, type τ); some ordinal is simultaneously the least stage of the tagged accessibility operator at the scalar tag of the canonical address of Q's class and the least stage of the scalar operator at that address; q is accessible under the confined strict relation, and every accessibility proof has rank ≤ that ordinal (`exact_ConfinedRankBelowTaggedStageNorm`).
- Assumes: nothing; frozen target sha256 fbc8dfa6…730b, receipt `1795402793153913589-3279202`, axioms propext/Classical.choice/Quot.sound; assembly of #1448 and #1455 at Γ = [] with the literal `tr` via `exact_GuardedQuoteLiteral`; no fixed-type-vs-whole-universe rank equality used.
- Serves: `thm:upper` — the printed chain rk_cs(s) ≤ rk_{R_S}(tr s) = inductive norm of tr(s), in one statement; remaining: the ID₁ derivation of the I-atom at that address and the norm theorem with a definition of BH.
