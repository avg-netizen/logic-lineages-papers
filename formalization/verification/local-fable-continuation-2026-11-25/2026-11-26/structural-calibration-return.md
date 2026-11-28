The saved patch analysis holds up, with one new fact: there is now a second, transitive consumer I had not seen. The saved closed constructor does not yield the literal shift front; the saved parameterized lemma does, and a short closed form of it is below. I changed nothing and ran nothing.

## Call sites of the packet theorem

- **Direct, one site.** `NumberedWindowInternalLiteralConcreteLambdaJoinedRulesProof.lean` imports the packet module (line 5), opens it by explicit name (line 49), and calls it at lines 114–115.
- **Transitive, one site.** `NativeModule/PersistentMarking/Paper16AccessibilityMilestoneInstalledPacket.lean` imports the rules module (line 3) and calls `exact_ConcreteLambdaJoinedRules` at lines 89–90 inside `exact_JoinedLambdaWindow`. It never names the packet theorem.
- **Effect of the patch.** The wrapper keeps the name and statement, and the `open` at line 49 is by explicit name, so neither site changes.

The second file already contains the packet-to-window step (`installedOfPacket`, `JoinedBetaWindow`). That supersedes the `windowOfPacket` definition I drafted earlier; that draft should not be added.

## `TermSyntaxCalibrated Va` versus `ActualRawSyntax Va`

The two propositions are:

- `TermSyntaxCalibrated V := ∀ n, run V n = (syntaxBits n).1.toNat` (`NumberedWindowInternalAuxExchangeMemoStepTargets:27`)
- `ActualRawSyntax p := ∀ q, evaluate p (q ::ᵥ nil) = ((syntaxBits q).1).toNat` (`NumberedWindowInternalSparseTypedRawTargets:24`)
- `run p n := evaluate p (n ::ᵥ nil)` (`NumberedWindowInternalSparsePathEnvelope:51`)

What I checked:

- **Syntactic difference.** Only `run V n` against `evaluate V (n ::ᵥ nil)`, plus the bound-variable name. The right-hand sides are the same term, and both use `NumberedWindowSyntaxAlgorithm.syntaxBits` and `List.Vector`.
- **Definitional equality.** It needs one unfolding each of `TermSyntaxCalibrated`, `ActualRawSyntax` and `run`. None is reducible, so `rw`, `simp` and reducible-transparency checks will not see it; ordinary type ascription and argument passing will.
- **Module visibility.** All three definitions sit in `@[expose] public section`, so their bodies are available to importers.
- **Statement scope.** The patch puts `ActualRawSyntax` into a public statement. It is publicly reachable from the packet module: line 3 publicly imports `…BetaLeafNumericProof`, which publicly imports `…BetaLeafProof`, which publicly imports `…SparseTypedRawTargets`.
- **Existing precedent.** Line 231 of the packet file already passes `rawSyntaxFit` where `ActualRawSyntax Va` is expected, in the same proof and with the same expected type. The patch's `mkFit Va rawSyntaxFit` is the same elaboration step.
- **One weaker spot.** The patch also uses `rawSyntaxFit` as a component of the final anonymous-constructor tuple. That should elaborate the same way, but it is the one use without a direct precedent.

A small hardening of the saved analysis removes that spot: convert once, by ascription, right after line 213, and use the converted name in both places.

```lean
  have vaFit : NumberedWindowInternalSparseTypedRawTargets.ActualRawSyntax Va := rawSyntaxFit
  have uFit : InstanceFit U := mkFit Va vaFit
  -- and in the final tuple: …,frontendInputs i L v₀,vaFit,rfl,uFit,
```

Downstream modules receive `ActualRawSyntax (unitAuxSyntax V tv)` directly and need no conversion.

## Does the saved constructor give the literal shift front?

- **`exact_SingletonLambdaInstanceConstructor` (lines 27–37): no.** Its program is `singletonLambda Vs H U` with `H` the opaque witness of `exact_LiteralShiftHit` and `U` the opaque witness of `exact_LiteralDepthInstance`. The beta rows in `…SingletonShiftHitInstallationProof` (lines 139–195) are stated for `zeroDepthInstance (singletonLambda V (shiftHitLiterals V H) (singletonBound V (shiftHitLiterals V H) U))`. That differs in both slots, so none of those rows apply. Even `exact_OpenBetaLambdaBoundHit` does not, since it needs the fallback slot to be `singletonBound V H U`.
- **`exact_SingletonLambdaLiteralsInstanceFit` (lines 42–53): yes.** Its program is that exact term with `V := Vs`. It is parameterized by `H`, `U` and their fits, so it is not yet a closed constructor.
- **Open side.** No bridge is needed there: `exact_OpenShiftHitLiteralsBound`, `…Free`, `…Bottom` and the `exact_OpenBetaLambdaShifted…` rows hold for every `H` and `U`, with only syntax hits as premises.

### The bridge

This closes the literal-front program over `H` and `U` in the same shape as the first constructor. Every name is already opened in the saved instance module, so it can go after line 53 with no new opens.

```lean
/-- The literal-front instance as a closed constructor: the shift and
fallback seeds are chosen first; for every calibrated syntax program the
program consumed by the shifted beta rows is calibrated at all depths
and its depth-zero wrapper is a beta instance. -/
theorem exact_SingletonLambdaLiteralsInstanceConstructor :
    ∃ (H : Program 2) (U : Program 3), ShiftHitFit H ∧ DepthInstanceFit U ∧
      ∀ Vs : Program 1, ActualRawSyntax Vs →
        DepthInstanceFit (singletonLambda Vs (shiftHitLiterals Vs H)
          (singletonBound Vs (shiftHitLiterals Vs H) U)) ∧
        InstanceFit (zeroDepthInstance (singletonLambda Vs (shiftHitLiterals Vs H)
          (singletonBound Vs (shiftHitLiterals Vs H) U))) := by
  obtain ⟨H,hFit⟩ := exact_LiteralShiftHit
  obtain ⟨U,uFit⟩ := exact_LiteralDepthInstance
  refine ⟨H,U,hFit,uFit,fun Vs vFit => ?_⟩
  have shiftFit := exact_ShiftHitLiteralsFit Vs H vFit hFit
  have slotFit : GuardedDepthInstanceFit (singletonBound Vs (shiftHitLiterals Vs H) U) :=
    exact_GuardedOfDepthInstanceFit _
      (exact_LiteralSingletonBoundGuardedCalibration Vs (shiftHitLiterals Vs H) U vFit shiftFit
        (exact_GuardedOfDepthInstanceFit U uFit))
  have fit := exact_LiteralSingletonLambdaCalibrationOfFallback Vs (shiftHitLiterals Vs H)
    (singletonBound Vs (shiftHitLiterals Vs H) U) vFit shiftFit slotFit
  exact ⟨fit,exact_ZeroDepthInstance _ fit⟩
```

After `obtain ⟨H,U,hFit,uFit,build⟩`, the packet arguments are:

```lean
(fun Vs => zeroDepthInstance (singletonLambda Vs (shiftHitLiterals Vs H)
  (singletonBound Vs (shiftHitLiterals Vs H) U)))
(fun Vs vFit => (build Vs vFit).2)
```

At `Vs := Va` the installed `U` is then the term the shifted beta rows are stated for, with `V := Va`.

## What is still missing for use at the window

- **The packet patch is unapplied.** Until `exact_ConcreteLambdaJoinedMemoPacketAt` exists, the constructor has no consumer.
- **The rules theorem loses the identity.** `exact_ConcreteLambdaJoinedRules` returns `∃ U … InstanceFit U` with no equation. It needs the same factoring at its line 114.
- **The window package loses it too.** `JoinedBetaWindow` (lines 45–53 of the installed-packet file) says only `∃ U, InstanceFit U ∧ …`. To apply any open row at a window, it needs a conjunct identifying `U` (or the shape of `A.raw`) with the constructor at that window's `Va`.
- **Syntax hits on argument and body.** The shifted rows need `unary Va (suc z) _` on the replacement and on the body nodes. The beta leaf checks `Va` only on the whole source and the target. In `…NormalizedAuxSyntaxProof` I found only the introduction direction for auxiliary nodes (`exact_OpenUnitAuxSyntaxIntro`); I did not search for an elimination lemma that would give hits on the parts.
