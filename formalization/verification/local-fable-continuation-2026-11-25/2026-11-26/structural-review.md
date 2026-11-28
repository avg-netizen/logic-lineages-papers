The proven fit does not reach any installed window today, for two reasons. No `InstalledWindow` value is constructed anywhere in the tree, and the one theorem that would feed one picks its beta instance from an opaque existential rather than `singletonLambda`. Below is an exact two-part bridge: an edit that lets the packet theorem take a supplied instance, and a new module that turns that packet into an `InstalledWindow` carrying the concrete program. Nothing here has been compiled, and I wrote no files.

## Dependency trace

- **Target side.** `InstalledWindow.installed` is `InstalledTupleAt S.entries (fixed S K) W scalar (jRaw scalar) cv tv (dCore scalar r permutation) application R least probes`, with `R := rawWithTarget scalar cv tv raw least`. `InstalledWindow` occurs only in `Paper16AccessibilityMilestoneTargets`.
- **Supplier.** `Packet.physical` in `NumberedWindowInternalLiteralDirectCarrierInstalledProof` has the same shape: same `jRaw`, `dCore`, `permutation`, `addressPositive`, and `Raw` is an abbreviation for `rawWithTarget`. A `Packet` at `xs := S.entries`, `s := fixed S K` therefore is an installed window.
- **Where the instance enters.** `exact_ConcreteLambdaJoinedMemoPacket` builds `raw := strictDualRaw C s (withBetaLeaf Va U leaves) (lambdaFallback other) …`. At line 191 it takes `U` from `exact_LiteralSingletonInstance : ∃ U : Program 2, InstanceFit U`.
- **How `U` is used.** Only through `uFit`, once, at line 231 (`exact_LiteralBetaLeafFit … Va U rawSyntaxFit uFit …`). Nothing else depends on which program `U` is.
- **Why the programs differ.** `Va := unitAuxSyntax V tv` is selected inside that proof, and the concrete instance must be built over the same `Va`. So the instance has to be supplied as a function of the syntax program.
- **My side.** `exact_LiteralSingletonLambdaCalibrationOfFallback` gives `DepthInstanceFit (singletonLambda Vs H U)` from `ActualRawSyntax Vs`, and `exact_ZeroDepthInstance` turns that into `InstanceFit`. `rawSyntaxFit` in the packet proof is `TermSyntaxCalibrated Va`, which the existing line 231 already passes where `ActualRawSyntax` is expected.

## Edit: `NumberedWindowInternalLiteralLambdaJoinedMemoPacketProof.lean`

Rename the existing theorem to `…At` with two extra parameters and a changed head, then restate the original as a corollary. The original statement is unchanged.

Replace the header (lines 155–182) with:

```lean
/-- The same packet for a supplied beta instance. The instance may depend
on the selected raw syntax program and is used only through its
`InstanceFit`; every other program and proof step is unchanged. -/
theorem exact_ConcreteLambdaJoinedMemoPacketAt (xs : Entries) (s : Settings) (P : List ProbeTy)
    (valid : ValidWindow s P) (seeds : WindowSeedsCovered s)
    (symmetric : HeadPairsSymmetric s.equivalentHeads) (grammar : GrammarTypeInclusion s)
    (included : ∀ ty ∈ finiteCodes P, ty ∈ s.window.1)
    (mk : Program 1 → Program 2)
    (mkFit : ∀ Vs : Program 1,
      NumberedWindowInternalSparseTypedRawTargets.ActualRawSyntax Vs → InstanceFit (mk Vs)) :
    ∃ (cv tv : Program 1) (leaves : Nat → Program 3) (other : Program 3)
      (baseX base : Program 2) (T V baseM : Program 1) (placed : Inputs),
      let Tg := selectedBiAuxType s T tv
      let Va := unitAuxSyntax V tv
      let U := mk Va
      let leaf := withBetaLeaf Va U leaves
      let C := measuredStrictCover V tv baseM
      let W := joinedAuxiliaryWindow s base Tg V tv baseM
      let raw := strictDualRaw C s leaf (lambdaFallback other) base base Tg Va Tg
      let Base := joinedBiAuxBase s baseX base Tg V tv baseM
      let E := recursiveTypedMemo Base
      let L := guardedLeast (headerLeast (fullAuxiliaryDecorator (packedLeastOn C E s)))
      let i := finiteScalar (addressScalar cv tv W L) (finiteCodes P)
      NumberedWindowInternalSparseTypedRawTargets.ActualRawSyntax Va ∧
      InstanceFit U ∧ Packet xs s P i cv tv (guardedRaw raw) L (applicationCore L) placed ∧
      placed.applicationGuard = applicationGuard i L ∧
      CanReverse Base ∧ WindowEndpoints W E ∧ Preserves E (packedLeastOn C E s) ∧
      MemoSelectedReports C s Base ∧ OpenRankTypeGuards P Tg tv ∧
      (∀ (c : Nat) (α : Type) (Γ : List (Formula α)) (f u y : OTerm α),
        let data := S i cv tv (rawWithTarget i cv tv (guardedRaw raw) L) L
        let B := sourceBody data c
        D B Γ (programGraph (applicationGuard i L) (suc z) ![f,u,y]) →
        D B Γ (carrier data false c y) ∧ D B Γ (atom neutralSource y)) := by
```

In the body, four line changes:

```lean
-- line 191: delete
  obtain ⟨U,uFit⟩ := exact_LiteralSingletonInstance

-- after line 194 (`let Va := unitAuxSyntax V tv`): insert
  let U := mk Va

-- after line 213 (`have rawSyntaxFit := …`): insert
  have uFit : InstanceFit U := mkFit Va rawSyntaxFit

-- line 268: replace the start of the final `refine`
  refine ⟨cv,tv,leaves,oldOtherLeaf,baseX,base,T,V,baseM,frontendInputs i L v₀,rawSyntaxFit,uFit,
```

Then add the original back, immediately after the `…At` theorem and with its original header (lines 158–182) verbatim:

```lean
theorem exact_ConcreteLambdaJoinedMemoPacket (xs : Entries) (s : Settings) (P : List ProbeTy)
    (valid : ValidWindow s P) (seeds : WindowSeedsCovered s)
    (symmetric : HeadPairsSymmetric s.equivalentHeads) (grammar : GrammarTypeInclusion s)
    (included : ∀ ty ∈ finiteCodes P, ty ∈ s.window.1) :
    -- conclusion exactly as at present lines 162–182
    := by
  obtain ⟨U,uFit⟩ := exact_LiteralSingletonInstance
  obtain ⟨cv,tv,leaves,other,baseX,base,T,V,baseM,placed,_,fit,rest⟩ :=
    exact_ConcreteLambdaJoinedMemoPacketAt xs s P valid seeds symmetric grammar included
      (fun _ => U) (fun _ _ => uFit)
  exact ⟨cv,tv,U,leaves,other,baseX,base,T,V,baseM,placed,fit,rest⟩
```

Add `#print axioms exact_ConcreteLambdaJoinedMemoPacketAt` beside the existing one.

## New module

Suggested path: `LogicLineages/NativeModule/PersistentMarking/Paper16InstalledLambdaInstanceProof.lean`

```lean
module
public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaJoinedMemoPacketProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaChildFitProof

@[expose] public section
namespace LogicLineages.PersistentMarking.Paper16InstalledLambdaInstanceProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules ID1Completion.SourcePresentation
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowFormulaCalibrationTargets NumberedWindowPresentationCheckers
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenA chosenH)
open NumberedWindowInternalSparseTuple (InstalledTupleAt)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open Paper16AccessibilityMilestoneTargets (InstalledWindow)
open NumberedWindowInternalLiteralCoveredMemo (WindowSeedsCovered)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowInternalSettingsGrammarGuardNumericTargets (GrammarTypeInclusion)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteCodes)
open NumberedWindowInternalLiteralDirectCarrierInstalledProof (Packet)
open NumberedWindowInternalLiteralAtomicRawGuardProof (guardedRaw)
open NumberedWindowInternalLiteralStrictDualChildProof (strictDualRaw)
open NumberedWindowInternalLiteralStrictMeasuredMemoTransportProof (selectedBiAuxType)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)
open NumberedWindowInternalLiteralBetaLeafProof (InstanceFit withBetaLeaf)
open NumberedWindowInternalLiteralLambdaFrameProof (lambdaFallback)
open NumberedWindowInternalLiteralLambdaJoinedMemoPacketProof (exact_ConcreteLambdaJoinedMemoPacketAt)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax)
open NumberedWindowInternalLiteralSingletonDepthNumericProof
  (DepthInstanceFit zeroDepthInstance exact_ZeroDepthInstance exact_LiteralDepthInstance)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (ShiftHitFit exact_LiteralShiftHit)
open NumberedWindowInternalLiteralSingletonGuardedCalibrationProof (exact_GuardedOfDepthInstanceFit)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambda)
open NumberedWindowInternalLiteralSingletonLambdaChildFitProof
  (exact_LiteralSingletonLambdaCalibrationOfFallback)

/-- A direct-carrier packet at the fixed settings of a source window is
literally an installed window: same programs, same installed tuple. -/
def windowOfPacket {S : Spine.Signature} {K : List Ty} {W : List ProbeTy}
    (valid : ValidWindow (fixed S K) W) (i cv tv : Program 1) (raw : Program 5)
    (L p₀ : Program 3) (v : Inputs)
    (packet : Packet S.entries (fixed S K) W i cv tv raw L p₀ v) : InstalledWindow S K W where
  valid := valid
  scalar := i
  contextGuard := cv
  typeGuard := tv
  raw := raw
  least := L
  application := p₀
  probes := v
  installed := packet.physical

/-- An installed window whose beta leaf carries the written lambda
instance over the window's own syntax program, together with that
program's proven all-depth fit. The four side conditions are exactly
those of the existing packet theorem at `fixed S K`. -/
theorem exact_InstalledLambdaInstanceWindow (S : Spine.Signature) (K : List Ty) (W : List ProbeTy)
    (valid : ValidWindow (fixed S K) W) (seeds : WindowSeedsCovered (fixed S K))
    (symmetric : HeadPairsSymmetric (fixed S K).equivalentHeads)
    (grammar : GrammarTypeInclusion (fixed S K))
    (included : ∀ ty ∈ finiteCodes W, ty ∈ (fixed S K).window.1) :
    ∃ (A : InstalledWindow S K W) (H : Program 2) (U : Program 3)
      (leaves : Nat → Program 3) (other : Program 3) (base : Program 2) (T V baseM : Program 1),
      let s := fixed S K
      let tv := A.typeGuard
      let Tg := selectedBiAuxType s T tv
      let Va := unitAuxSyntax V tv
      let C := measuredStrictCover V tv baseM
      let leaf := withBetaLeaf Va (zeroDepthInstance (singletonLambda Va H U)) leaves
      ActualRawSyntax Va ∧ ShiftHitFit H ∧ DepthInstanceFit U ∧
      DepthInstanceFit (singletonLambda Va H U) ∧
      A.raw = guardedRaw (strictDualRaw C s leaf (lambdaFallback other) base base Tg Va Tg) := by
  obtain ⟨H,hFit⟩ := exact_LiteralShiftHit
  obtain ⟨U,uFit⟩ := exact_LiteralDepthInstance
  obtain ⟨cv,tv,leaves,other,baseX,base,T,V,baseM,placed,vFit,_,packet,_⟩ :=
    exact_ConcreteLambdaJoinedMemoPacketAt S.entries (fixed S K) W valid seeds symmetric grammar
      included (fun Vs => zeroDepthInstance (singletonLambda Vs H U))
      (fun Vs vFit => exact_ZeroDepthInstance (singletonLambda Vs H U)
        (exact_LiteralSingletonLambdaCalibrationOfFallback Vs H U vFit hFit
          (exact_GuardedOfDepthInstanceFit U uFit)))
  exact ⟨windowOfPacket valid _ cv tv _ _ _ placed packet,H,U,leaves,other,base,T,V,baseM,
    vFit,hFit,uFit,
    exact_LiteralSingletonLambdaCalibrationOfFallback _ H U vFit hFit
      (exact_GuardedOfDepthInstanceFit U uFit),rfl⟩

#print axioms windowOfPacket
#print axioms exact_InstalledLambdaInstanceWindow
end LogicLineages.PersistentMarking.Paper16InstalledLambdaInstanceProof
```

## What remains open

- **Window selection.** `SelectInstalledWindows` now reduces, for the concrete instance, to choosing for each closed `S, K` a `W` satisfying the five hypotheses of the theorem at `fixed S K`. Those are `ValidWindow`, `WindowSeedsCovered`, `HeadPairsSymmetric`, `GrammarTypeInclusion`, and `included`. I did not look for providers of these; `TARGETS.md` calls it the mixed-window selection problem.
- **Rules at this instance.** `exact_ConcreteLambdaJoinedRules` still destructures the existential packet, so its `BetaJoinedRulesAt … U …` is for the opaque `U`. It needs the same change: take `mk`/`mkFit`, call the `…At` packet, and set `U := mk Va`. Its proof mentions `U` only in `exact_OpenJoinedBetaOutcome` and the conclusion.
- **The fallback slot is still opaque.** `H` and the inner `U` come from `exact_LiteralShiftHit` and `exact_LiteralDepthInstance`. Only the atom, bound and lambda rows of the installed instance are physical.

## Compile risks

- **Syntax-fit coercion.** The `…At` edit passes `rawSyntaxFit : TermSyntaxCalibrated Va` where `ActualRawSyntax Va` is expected, in `mkFit` and in the result tuple. The existing line 231 already relies on that conversion.
- **Corollary shape.** The restated original and the new theorem both destructure and rebuild through the `let` chain. The compiled destructuring in `exact_ConcreteLambdaJoinedRules` uses the same pattern.
- **Final `rfl`.** In `exact_InstalledLambdaInstanceWindow` it must unfold `windowOfPacket` and beta-reduce the supplied instance function.
- **`Ty` resolution.** The new module copies the `open` block of `Paper16AccessibilityMilestoneTargets` so `Spine.Signature`, `Ty` and `fixed` resolve as they do there. I did not verify which `Ty` that is.
- **Co-import.** I did not verify that the packet module and `Paper16AccessibilityMilestoneTargets` can be imported together.
