The packet file is unchanged since I last read it (281 lines), so the positions below are against the current text. Nothing has been written or compiled.

## Parameter type

The bare `∀ Vs, ActualRawSyntax Vs → ∃ U, InstanceFit U` is not usable. It is provable outright (`fun _ _ => exact_LiteralSingletonInstance`), so a theorem taking it is equivalent to the existing one. The conclusion could still only say `∃ U`, because a program cannot be named out of an existential hypothesis.

The smallest form that fixes the program is a function with a fit under the syntax premise:

```lean
(mk : Program 1 → Program 2)
(mkFit : ∀ Vs : Program 1, ActualRawSyntax Vs → InstanceFit (mk Vs))
```

`mk` cannot usefully depend on the proof, and the fit must be quantified over `Vs` because `Va` is chosen inside the proof.

## Verification of `Va`

- **Definition.** Line 165 (statement) and line 194 (proof): `Va := unitAuxSyntax V tv`. `V` comes from `exact_SelectedFactoredCover` (line 187) and `tv` from `exact_ConcretePairedCoveredTypedAuxTuple` (line 183).
- **Its fit.** Line 213: `rawSyntaxFit := exact_LiteralUnitAuxSyntax V tv vFit calls.2.1 : TermSyntaxCalibrated (unitAuxSyntax V tv)`.
- **Same proposition as `ActualRawSyntax Va`.** The two definitions differ only by unfolding `run`:
  - `TermSyntaxCalibrated V := ∀ n, run V n = (syntaxBits n).1.toNat` (`NumberedWindowInternalAuxExchangeMemoStepTargets:27`).
  - `run p n := evaluate p (n ::ᵥ nil)` (`NumberedWindowInternalSparsePathEnvelope:51`).
  - `ActualRawSyntax p := ∀ q, evaluate p (q ::ᵥ nil) = ((syntaxBits q).1).toNat` (`NumberedWindowInternalSparseTypedRawTargets:24`).
  - Line 231 already passes `rawSyntaxFit` where `ActualRawSyntax Va` is expected, so the conversion is exercised by the compiled proof.
- **Where `U` meets `Va`.** Only lines 196 (`leaf := withBetaLeaf Va U leaves`) and 231. The other uses of `Va` (lines 215, 217, 221, 222, 237–239, 258) do not involve `U`.
- **Consequence.** With `mk Va`, the instance's syntax guard and the beta leaf's syntax program are the same `Va`.

## Edits to `LogicLineages/PersistentMarking/NumberedWindowInternalLiteralLambdaJoinedMemoPacketProof.lean`

```diff
@@ line 153: add one open after it
 open NumberedWindowInternalLiteralLambdaFrameNumericProof (exact_LiteralLambdaFallback)
+open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax)

@@ lines 155-166: docstring, name, parameters, binder list, one new let
-/-- The original beta root and contextual lambda callback are now
-both literal, with all originating numeric answers recalibrated.
-Neither descends under a binder at a fabricated context. -/
-theorem exact_ConcreteLambdaJoinedMemoPacket (xs : Entries) (s : Settings) (P : List ProbeTy)
+/-- The lambda joined packet for a supplied beta instance. The instance
+is a function of the selected raw syntax program and is used only
+through its `InstanceFit`; every other program and step is unchanged. -/
+theorem exact_ConcreteLambdaJoinedMemoPacketAt (xs : Entries) (s : Settings) (P : List ProbeTy)
     (valid : ValidWindow s P) (seeds : WindowSeedsCovered s)
     (symmetric : HeadPairsSymmetric s.equivalentHeads) (grammar : GrammarTypeInclusion s)
-    (included : ∀ ty ∈ finiteCodes P, ty ∈ s.window.1) :
-    ∃ (cv tv : Program 1) (U : Program 2) (leaves : Nat → Program 3) (other : Program 3)
+    (included : ∀ ty ∈ finiteCodes P, ty ∈ s.window.1)
+    (mk : Program 1 → Program 2)
+    (mkFit : ∀ Vs : Program 1, ActualRawSyntax Vs → InstanceFit (mk Vs)) :
+    ∃ (cv tv : Program 1) (leaves : Nat → Program 3) (other : Program 3)
       (baseX base : Program 2) (T V baseM : Program 1) (placed : Inputs),
       let Tg := selectedBiAuxType s T tv
       let Va := unitAuxSyntax V tv
+      let U := mk Va
       let leaf := withBetaLeaf Va U leaves

@@ line 174: export the syntax fit of Va
+      ActualRawSyntax Va ∧
       InstanceFit U ∧ Packet xs s P i cv tv (guardedRaw raw) L (applicationCore L) placed ∧

@@ lines 191-195: drop the existential choice, bind U to the constructor
-  obtain ⟨U,uFit⟩ := exact_LiteralSingletonInstance
   have calls := orig.physical.2.2.1
   let Tg := selectedBiAuxType s T tv
   let Va := unitAuxSyntax V tv
+  let U := mk Va
   let leaves := leafAtAuxiliary oldLeaf

@@ line 213: obtain the instance fit from the fixed Va
   have rawSyntaxFit := exact_LiteralUnitAuxSyntax V tv vFit calls.2.1
+  have uFit : InstanceFit U := mkFit Va rawSyntaxFit

@@ line 268: result tuple without U, with the syntax fit
-  refine ⟨cv,tv,U,leaves,oldOtherLeaf,baseX,base,T,V,baseM,frontendInputs i L v₀,uFit,
+  refine ⟨cv,tv,leaves,oldOtherLeaf,baseX,base,T,V,baseM,frontendInputs i L v₀,rawSyntaxFit,uFit,

@@ after line 277: the wrapper, original docstring and statement verbatim
+
+/-- The original beta root and contextual lambda callback are now
+both literal, with all originating numeric answers recalibrated.
+Neither descends under a binder at a fabricated context. -/
+theorem exact_ConcreteLambdaJoinedMemoPacket (xs : Entries) (s : Settings) (P : List ProbeTy)
+    (valid : ValidWindow s P) (seeds : WindowSeedsCovered s)
+    (symmetric : HeadPairsSymmetric s.equivalentHeads) (grammar : GrammarTypeInclusion s)
+    (included : ∀ ty ∈ finiteCodes P, ty ∈ s.window.1) :
+    ∃ (cv tv : Program 1) (U : Program 2) (leaves : Nat → Program 3) (other : Program 3)
+      (baseX base : Program 2) (T V baseM : Program 1) (placed : Inputs),
+      -- present lines 164–182, unchanged
+      := by
+  obtain ⟨U,uFit⟩ := exact_LiteralSingletonInstance
+  obtain ⟨cv,tv,leaves,other,baseX,base,T,V,baseM,placed,_,_,rest⟩ :=
+    exact_ConcreteLambdaJoinedMemoPacketAt xs s P valid seeds symmetric grammar included
+      (fun _ => U) (fun _ _ => uFit)
+  exact ⟨cv,tv,U,leaves,other,baseX,base,T,V,baseM,placed,uFit,rest⟩

@@ line 279
+#print axioms exact_ConcreteLambdaJoinedMemoPacketAt
 #print axioms exact_ConcreteLambdaJoinedMemoPacket
```

The `ActualRawSyntax Va` conjunct is not needed by the packet itself. It is there so a caller can recover the all-depth fit of the inner program, which `InstanceFit (mk Va)` alone does not give.

The only caller I found is `exact_ConcreteLambdaJoinedRules` (`…ConcreteLambdaJoinedRulesProof`, lines 114–115). It destructures the wrapper's unchanged statement, so it needs no edit.

## Reusing the numeric singleton fit

A small new module supplies the constructor and its fit from the saved calibration. Suggested path: `LogicLineages/PersistentMarking/NumberedWindowInternalLiteralSingletonLambdaInstanceProof.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaChildFitProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaInstanceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax)
open NumberedWindowInternalLiteralBetaLeafProof (InstanceFit)
open NumberedWindowInternalLiteralSingletonDepthNumericProof (zeroDepthInstance exact_ZeroDepthInstance)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (ShiftHitFit)
open NumberedWindowInternalLiteralSingletonGuardedCalibrationProof (GuardedDepthInstanceFit)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambda)
open NumberedWindowInternalLiteralSingletonLambdaChildFitProof
  (exact_LiteralSingletonLambdaCalibrationOfFallback)

/-- The written lambda instance at depth zero, as a function of the
syntax program it guards with. -/
def singletonLambdaInstanceOf (H : Program 2) (U : Program 3) (Vs : Program 1) : Program 2 :=
  zeroDepthInstance (singletonLambda Vs H U)

theorem exact_SingletonLambdaInstanceOfFit (H : Program 2) (U : Program 3)
    (hFit : ShiftHitFit H) (uFit : GuardedDepthInstanceFit U)
    (Vs : Program 1) (vFit : ActualRawSyntax Vs) :
    InstanceFit (singletonLambdaInstanceOf H U Vs) :=
  exact_ZeroDepthInstance (singletonLambda Vs H U)
    (exact_LiteralSingletonLambdaCalibrationOfFallback Vs H U vFit hFit uFit)

#print axioms singletonLambdaInstanceOf
#print axioms exact_SingletonLambdaInstanceOfFit
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaInstanceProof
```

The selection is then one application:

```lean
exact_ConcreteLambdaJoinedMemoPacketAt xs s P valid seeds symmetric grammar included
  (singletonLambdaInstanceOf H U) (exact_SingletonLambdaInstanceOfFit H U hFit uFit)
```

Its result has `U := singletonLambdaInstanceOf H U Va`, which unfolds to `zeroDepthInstance (singletonLambda Va H U)`, and `ActualRawSyntax Va` as the first conjunct. The `Paper16InstalledLambdaInstanceProof` draft from last turn can pass these two arguments in place of its inline lambdas with no other change.

## Compile risks

- **`mkFit Va rawSyntaxFit`.** Depends on the same `TermSyntaxCalibrated`-to-`ActualRawSyntax` conversion as line 231, now also used for the new first conjunct.
- **Wrapper.** It destructures through the `let` chain and rebuilds the original tuple. `rest` mentions `(fun _ => U) Va` where the target has `U`; that must reduce.
- **Local `let U`.** In the `…At` body `U` is a local definition rather than a variable. Lines 196 and 231 use it exactly as before.
- **Import cycle.** The new module imports only the child-fit module, and the packet module's own imports (lines 2–38) contain no Singleton module. I did not trace the packet's transitive imports.
