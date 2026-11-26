module

public import LogicLineages.NativeModule.PersistentMarking.NativeTowerTargets
public import LogicLineages.NativeModule.PersistentMarking.ClosingProof
public import LogicLineages.NativeModule.PersistentMarking.ClosedSyntaxProof

@[expose] public section

/-! Typing and de Bruijn substitution for the native towers: every partial tower is closed
native, and substituting a closed term into the tower body acts slot by slot. -/

namespace LogicLineages.PersistentMarking.NativeTowerSyntaxProof
open Spine NameBridge NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorTargets NativeIteratorStrictTargets NativeTowerTargets
open OrdinalRealizationTargets NativeOrdinalRealizationTargets

/-! ## Typing -/

structure NativeIn (S : Signature) (C : BoundContext) (q : Expr) (τ : Ty) : Prop where
  typed : Typed C q τ
  valid : Valid S q
  ordinary : Ordinary q
  closed : Closed q
  native : Native q

theorem closedIn {S q τ} (C : BoundContext) (h : ClosedNative S q τ) : NativeIn S C q τ :=
  ⟨ClosingProof.weakening q τ h.1.1.1 C, h.1.1.2, h.1.2.1, h.1.2.2, h.2⟩

theorem close {S q τ} (h : NativeIn S EmptyContext q τ) : ClosedNative S q τ :=
  ⟨⟨⟨h.typed, h.valid⟩, h.ordinary, h.closed⟩, h.native⟩

theorem boundIn (S : Signature) (C : BoundContext) (σ : Ty) (k : Nat)
    (h : C k = some σ) : NativeIn S C (.bound σ k) σ :=
  ⟨.bound h, True.intro, True.intro, fun _ => rfl, fun _ _ => by simp [DecisionInventory.heads]⟩

theorem appIn {S C σ τ f a}
    (hf : NativeIn S C f (.arrow σ τ)) (ha : NativeIn S C a σ) :
    NativeIn S C (app σ τ f a) τ where
  typed := .head (.cons hf.typed (.cons ha.typed .nil))
  valid := ⟨⟨0, rfl⟩, hf.valid, ha.valid, True.intro⟩
  ordinary := ⟨hf.ordinary, ha.ordinary, True.intro⟩
  closed := fun name => by simp [app, freeOccurs, freeOccursArgs, hf.closed name, ha.closed name]
  native := fun name arity => by
    simp [app, DecisionInventory.heads, DecisionInventory.headsArgs, hf.native name arity, ha.native name arity]

theorem lamIn {S C σ τ body} (h : NativeIn S (C.push σ) body τ) :
    NativeIn S C (.lam σ body) (.arrow σ τ) :=
  ⟨.lam h.typed, h.valid, h.ordinary, h.closed, h.native⟩

theorem iteratorIn {S C} (A : SemanticType) {i p u : Expr} (hi : NativeIn S C i indexType)
    (hp : NativeIn S C p (functionType A)) (hu : NativeIn S C u (actualType A)) :
    NativeIn S C (applied A i p u) (actualType A) :=
  appIn (appIn (appIn (closedIn C (NativeIteratorChecks.exact_ClosedNativeIterator S A)) hi) hp) hu

theorem zeroIn (S : Signature) (C : BoundContext) : NativeIn S C towerZero indexType :=
  lamIn (boundIn S (C.push .ground) .ground 0 rfl)

theorem zeroClosed (S : Signature) : ClosedNative S towerZero indexType := close (zeroIn S EmptyContext)

/-- Push the binder types `|A_k|, …, |A_1|` (outermost first). -/
def pushAll (C : BoundContext) : Nat → BoundContext
  | 0 => C
  | k + 1 => pushAll (C.push (tierType (k+1))) k

theorem pushAll_high (C : BoundContext) (k i : Nat) : pushAll C k (k + i) = C i := by
  induction k generalizing C i with
  | zero => simp [pushAll]
  | succ k ih =>
    show pushAll (C.push (tierType (k+1))) k (k + 1 + i) = C i
    rw [show k + 1 + i = k + (i + 1) by omega, ih]
    rfl

theorem pushAll_low (C : BoundContext) (k j : Nat) (h : j < k) :
    pushAll C k j = some (tierType (j+1)) := by
  induction k generalizing C with
  | zero => omega
  | succ k ih =>
    show pushAll (C.push (tierType (k+1))) k j = _
    by_cases hj : j < k
    · exact ih _ hj
    · have hjk : j = k := by omega
      subst hjk
      exact pushAll_high (C.push (tierType (j+1))) j 0

theorem natDownIn {S D} (m : Nat) {v : Expr} {a : Nat → Expr}
    (hv : NativeIn S D v (tierType (m+1)))
    (ha : ∀ j, 1 ≤ j → j ≤ m → NativeIn S D (a j) (tierType j)) :
    NativeIn S D (natDown m v a) indexType := by
  induction m generalizing v with
  | zero => exact appIn hv (zeroIn S D)
  | succ m ih =>
    exact ih (appIn hv (ha (m+1) (by omega) (by omega))) (fun j h1 h2 => ha j h1 (by omega))

theorem spineIn {S D} (l : Nat) {alpha : Expr} {a : Nat → Expr}
    (hα : NativeIn S D alpha indexType)
    (ha : ∀ j, 1 ≤ j → j ≤ l + 1 → NativeIn S D (a j) (tierType j)) :
    NativeIn S D (spine l alpha a) indexType := by
  cases l with
  | zero => exact iteratorIn (nativeShape (tier 0)) hα (ha 1 (by omega) (by omega)) (zeroIn S D)
  | succ m =>
    exact natDownIn m (iteratorIn (nativeShape (tier (m+1))) hα (ha (m+2) (by omega) (by omega))
      (ha (m+1) (by omega) (by omega))) (fun j h1 h2 => ha j h1 (by omega))

theorem bindersIn {S} (k : Nat) {C : BoundContext} {X : Expr}
    (hX : NativeIn S (pushAll C k) X (tierType 1)) :
    NativeIn S C (binders k X) (tierType (k+1)) := by
  induction k generalizing C with
  | zero => exact hX
  | succ k ih => exact lamIn (ih (C := C.push (tierType (k+1))) hX)

theorem fixBodyIn {S D} {F : Expr} (l : Nat) {a : Nat → Expr} (hF : ClosedNative S F (tierType 2))
    (hSp : NativeIn S (D.push indexType) (spine l (.bound indexType 0) a) indexType) :
    NativeIn S D (fixBody F l a) (tierType 1) :=
  appIn (closedIn D hF) (lamIn hSp)

/-- Every partial tower: slots `≤ k` bound, slots `> k` closed native. -/
theorem partialClosed (S : Signature) {F : Expr} (hF : ClosedNative S F (tierType 2)) (l k : Nat)
    (a : Nat → Expr) (hb : ∀ j, 1 ≤ j → j ≤ k → a j = boundSlots j)
    (hc : ∀ j, k < j → j ≤ l + 1 → ClosedNative S (a j) (tierType j)) :
    ClosedNative S (binders k (fixBody F l a)) (tierType (k+1)) := by
  let D : BoundContext := (pushAll EmptyContext k).push indexType
  have slots : ∀ j, 1 ≤ j → j ≤ l + 1 → NativeIn S D (a j) (tierType j) := by
    intro j h1 h2
    by_cases hjk : j ≤ k
    · rw [hb j h1 hjk]
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      exact boundIn S D _ _ (pushAll_low EmptyContext k i (by omega))
    · exact closedIn D (hc j (by omega) h2)
  exact close (bindersIn k (fixBodyIn l hF (spineIn l (boundIn S D indexType 0 rfl) slots)))

theorem towerClosed (S : Signature) {F : Expr} (hF : ClosedNative S F (tierType 2)) (l : Nat) :
    ClosedNative S (towerTerm F l) (tierType (l+2)) :=
  partialClosed S hF l (l+1) boundSlots (fun _ _ _ => rfl) (fun j h1 h2 => by omega)

theorem lambdaSpineClosed (S : Signature) (l : Nat) (a : Nat → Expr)
    (hc : ∀ j, 1 ≤ j → j ≤ l + 1 → ClosedNative S (a j) (tierType j)) :
    ClosedNative S (.lam indexType (spine l (.bound indexType 0) a)) (.arrow indexType indexType) := by
  let D : BoundContext := EmptyContext.push indexType
  exact close (lamIn (spineIn l (boundIn S D indexType 0 rfl) (fun j h1 h2 => closedIn D (hc j h1 h2))))

/-! ## Substitution -/

theorem unchanged {q τ} (h : Typed EmptyContext q τ) (values : Args) (depth : Nat) :
    substitute values depth q = q :=
  (ClosedSyntaxProof.term EmptyContext depth (fun _ _ hx => by cases hx) q τ h 0 values).2

theorem substApp (values : Args) (depth : Nat) (σ τ : Ty) (q a : Expr) :
    substitute values depth (app σ τ q a) =
      app σ τ (substitute values depth q) (substitute values depth a) := rfl

theorem substLam (values : Args) (depth : Nat) (σ : Ty) (b : Expr) :
    substitute values depth (.lam σ b) = .lam σ (substitute values (depth+1) b) := rfl

theorem nearer (values : Args) (τ : Ty) (i depth : Nat) (h : i < depth) :
    substitute values depth (.bound τ i) = .bound τ i := by
  simp only [substitute, h, if_true]

theorem atSlot {u : Expr} {σ τ : Ty} (hu : Typed EmptyContext u σ) (depth : Nat) :
    substitute (.cons u .nil) depth (.bound τ depth) = u := by
  simp only [substitute, Nat.lt_irrefl, if_false, Nat.sub_self, Args.get,
    ClosedSyntaxProof.closedShift u σ hu depth]

theorem substZero (S : Signature) (values : Args) (depth : Nat) :
    substitute values depth towerZero = towerZero :=
  unchanged (zeroClosed S).1.1.1 values depth

theorem substApplied (S : Signature) (values : Args) (depth : Nat) (A : SemanticType) (i p u : Expr) :
    substitute values depth (applied A i p u) =
      applied A (substitute values depth i) (substitute values depth p) (substitute values depth u) := by
  have original := (NativeIteratorChecks.exact_ClosedNativeIterator S A).1.1.1
  simp only [applied, substApp, unchanged original values depth]

theorem substNatDown (S : Signature) (values : Args) (depth m : Nat) (v : Expr) (a : Nat → Expr) :
    substitute values depth (natDown m v a) =
      natDown m (substitute values depth v) (fun j => substitute values depth (a j)) := by
  induction m generalizing v with
  | zero =>
    show substitute values depth (app indexType indexType v towerZero) = _
    rw [substApp, substZero S]
    rfl
  | succ m ih =>
    show substitute values depth (natDown m (app (tierType (m+1)) (tierType (m+1)) v (a (m+1))) a) = _
    rw [ih, substApp]
    rfl

theorem substSpine (S : Signature) (values : Args) (depth l : Nat) (alpha : Expr) (a : Nat → Expr) :
    substitute values depth (spine l alpha a) =
      spine l (substitute values depth alpha) (fun j => substitute values depth (a j)) := by
  cases l with
  | zero =>
    show substitute values depth (applied (nativeShape (tier 0)) alpha (a 1) towerZero) = _
    rw [substApplied S, substZero S]
    rfl
  | succ m =>
    show substitute values depth
      (natDown m (applied (nativeShape (tier (m+1))) alpha (a (m+2)) (a (m+1))) a) = _
    rw [substNatDown S, substApplied S]
    rfl

theorem substBinders (values : Args) (depth k : Nat) (X : Expr) :
    substitute values depth (binders k X) = binders k (substitute values (depth + k) X) := by
  induction k generalizing depth with
  | zero => rfl
  | succ k ih =>
    show substitute values depth (.lam (tierType (k+1)) (binders k X)) = _
    rw [substLam, ih, show depth + 1 + k = depth + (k + 1) by omega]
    rfl

theorem substFixBody (S : Signature) {F : Expr} (hF : ClosedNative S F (tierType 2))
    (values : Args) (depth l : Nat) (a : Nat → Expr) :
    substitute values depth (fixBody F l a) =
      fixBody F l (fun j => substitute values (depth + 1) (a j)) := by
  unfold fixBody
  rw [substApp, substLam, substSpine S, unchanged hF.1.1.1,
    nearer values indexType 0 (depth + 1) (by omega)]

end LogicLineages.PersistentMarking.NativeTowerSyntaxProof
