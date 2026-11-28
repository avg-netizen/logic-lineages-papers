The packet file is still unchanged (281 lines) and the instance module is saved with the names I gave, so the patch below is against the current text. Nothing has been written or compiled.

One difference from my earlier sketch: to keep the quantifier prefix untouched, `U` stays in the existential and is pinned by an equation `U = mk Va`, instead of being replaced by a `let`. The `mk`/`mkFit` signatures are as before.

## Where the instance fit travels in the real packet

All line numbers are in `NumberedWindowInternalLiteralLambdaJoinedMemoPacketProof.lean`.

1. Lines 183 and 187 select `tv` and `V`; line 194 fixes `Va := unitAuxSyntax V tv`.
2. Line 213 proves `rawSyntaxFit`, the syntax fit of `Va`.
3. **New:** `uFit := mkFit Va rawSyntaxFit`. With the saved constructor this is `(build Va rawSyntaxFit).2 : InstanceFit (zeroDepthInstance (singletonLambda Va H U₃))`.
4. Line 196 forms `leaf := withBetaLeaf Va U leaves`; line 231 turns `uFit` into `LeafFit` for that leaf.
5. Lines 232–239 lift it to the root fit and then to the raw calibration of `strictDualRaw C s leaf …`.
6. Lines 240–250 reinstall raw, least, application and scalar; lines 268–270 return the `Packet`, whose `physical` field is the installed tuple.

`uFit` is used nowhere else, so replacing the existential choice at line 191 changes nothing downstream.

## Patch

```diff
--- LogicLineages/PersistentMarking/NumberedWindowInternalLiteralLambdaJoinedMemoPacketProof.lean

@@ lines 155-161: docstring, name, two new parameters
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
+    (included : ∀ ty ∈ finiteCodes P, ty ∈ s.window.1)
+    (mk : Program 1 → Program 2)
+    (mkFit : ∀ Vs : Program 1,
+      NumberedWindowInternalSparseTypedRawTargets.ActualRawSyntax Vs → InstanceFit (mk Vs)) :

@@ lines 162-173: unchanged (same existential prefix, same lets)

@@ line 174: two conjuncts in front
+      NumberedWindowInternalSparseTypedRawTargets.ActualRawSyntax Va ∧ U = mk Va ∧
       InstanceFit U ∧ Packet xs s P i cv tv (guardedRaw raw) L (applicationCore L) placed ∧

@@ lines 191-195: drop the existential choice, bind U to the constructor
-  obtain ⟨U,uFit⟩ := exact_LiteralSingletonInstance
   have calls := orig.physical.2.2.1
   let Tg := selectedBiAuxType s T tv
   let Va := unitAuxSyntax V tv
+  let U := mk Va
   let leaves := leafAtAuxiliary oldLeaf

@@ line 213: instance fit at the fixed Va
   have rawSyntaxFit := exact_LiteralUnitAuxSyntax V tv vFit calls.2.1
+  have uFit : InstanceFit U := mkFit Va rawSyntaxFit

@@ line 268: two extra components after the witnesses
-  refine ⟨cv,tv,U,leaves,oldOtherLeaf,baseX,base,T,V,baseM,frontendInputs i L v₀,uFit,
+  refine ⟨cv,tv,U,leaves,oldOtherLeaf,baseX,base,T,V,baseM,frontendInputs i L v₀,rawSyntaxFit,rfl,uFit,

@@ after line 277: wrapper with the original docstring and statement
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
+      -- present lines 164–182, copied unchanged
+      := by
+  obtain ⟨U₀,uFit⟩ := exact_LiteralSingletonInstance
+  obtain ⟨cv,tv,U,leaves,other,baseX,base,T,V,baseM,placed,_,_,rest⟩ :=
+    exact_ConcreteLambdaJoinedMemoPacketAt xs s P valid seeds symmetric grammar included
+      (fun _ => U₀) (fun _ _ => uFit)
+  exact ⟨cv,tv,U,leaves,other,baseX,base,T,V,baseM,placed,rest⟩

@@ line 279
+#print axioms exact_ConcreteLambdaJoinedMemoPacketAt
 #print axioms exact_ConcreteLambdaJoinedMemoPacket
```

That is seven changed or inserted lines in the existing statement and body, plus the wrapper. The wrapper's hypotheses, quantifier prefix and conclusion are the current ones verbatim, so `exact_ConcreteLambdaJoinedRules` (lines 114–115 of `…ConcreteLambdaJoinedRulesProof`, the only caller) needs no edit.

## Use at the real packet with the saved instance

A consumer writes the following; the pattern is the existing one at `…ConcreteLambdaJoinedRulesProof:114` with two names inserted after `placed`:

```lean
  obtain ⟨H,U₃,hFit,uFit₃,build⟩ := exact_SingletonLambdaInstanceConstructor
  obtain ⟨cv,tv,U,leaves,other₀,X,base,T,V,baseM,placed,vFit,same,fit,packet,placedApp,
      reverse,ends,stable,selected,guards,closed⟩ :=
    exact_ConcreteLambdaJoinedMemoPacketAt xs s P valid seeds symmetric grammar included
      (fun Vs => zeroDepthInstance (singletonLambda Vs H U₃))
      (fun Vs vFit => (build Vs vFit).2)
```

This yields:

- `same : U = zeroDepthInstance (singletonLambda (unitAuxSyntax V tv) H U₃)`, the installed instance identified.
- `vFit : ActualRawSyntax (unitAuxSyntax V tv)`, so `(build _ vFit).1` is the all-depth fit of the installed inner program.
- `fit`, `packet` and the rest exactly as the existing caller receives them.

Because `U` keeps its position, a parameterized version of `exact_ConcreteLambdaJoinedRules` can reuse its present lines 116–166 unchanged after this `obtain`. For the physical-front variant, the two arguments are the constructor in the statement of `exact_SingletonLambdaLiteralsInstanceFit` and that lemma applied to `H`, `U₃`, `hFit` and the guarded form of `uFit₃`.

## Compile risks

- **`mkFit Va rawSyntaxFit` and the first new component.** Both hand a `TermSyntaxCalibrated Va` proof where `ActualRawSyntax Va` is expected. Line 231 already does this.
- **`rfl` in the result tuple.** It must see through the local definition `U := mk Va`.
- **Wrapper.** `rest` is passed whole as the body of the existential; it is the same conjunction with the `let`s instantiated.
- **Qualified name.** I wrote `NumberedWindowInternalSparseTypedRawTargets.ActualRawSyntax` in full rather than adding an `open`, to avoid any clash with the many namespaces this file opens whole.
