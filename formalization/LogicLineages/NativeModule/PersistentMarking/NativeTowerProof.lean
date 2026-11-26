module

public import LogicLineages.NativeModule.PersistentMarking.NativeTowerSyntaxProof
public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalRealizationProof
public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalIterationProof
public import LogicLineages.NativeModule.PersistentMarking.NativeClosedBetaChecks
public import LogicLineages.NativeModule.PersistentMarking.NativeClosedStrictWellFoundedChecks

@[expose] public section

/-! Realization of every finite-type extractor `B_l` by its printed native term
(ordinals.tex 531–550), by downward induction on the number of remaining binders.
Ingredients: the abstraction rule `exact_NativeLambdaRealization`, closed native beta
`exact_ClosedNativeBeta` (to name the substituted body), the iterator theorem
`exact_NativeIteratorRealizesFullPrefix` with orbit uniqueness `exact_FullPrefixOrbitExists`,
and application, which is the definition of arrow realization. -/

namespace LogicLineages.PersistentMarking.NativeTowerProof
open Spine NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets NativeIteratorTargets
open NativeIteratorStrictTargets NativeClosedApplication
open OrdinalRealizationTargets NativeOrdinalRealizationTargets NativeOrdinalIterationTargets
open OrdinalNativeOrbitProof NativeTowerTargets NativeTowerSyntaxProof

/-- The well-foundedness proof used throughout (any two are equal by proof irrelevance). -/
abbrev wfOf (S : Signature) : WellFounded (@NativeBelow S indexType) :=
  NativeClosedStrictWellFoundedChecks.exact_ClosedNativeStrictWellFounded S indexType

theorem transfer {S A} {t t' : (nativeTerms S).term A} {x : Value A} (e : t.val = t'.val)
    (h : Realizes (nativeTerms S) (wfOf S) A t' x) : Realizes (nativeTerms S) (wfOf S) A t x := by
  rw [Subtype.ext e]
  exact h

/-- The abstraction rule, with the substituted body named by closed native beta. -/
theorem lambdaRule (S : Signature) (A D : FiniteType) (body : Expr)
    (hl : ClosedNative S (.lam (actualType (nativeShape A)) body)
      (.arrow (actualType (nativeShape A)) (actualType (nativeShape D))))
    (f : Value A → Value D)
    (H : ∀ (x : Value A) (u : (nativeTerms S).term A), Realizes (nativeTerms S) (wfOf S) A u x →
      ∀ v : (nativeTerms S).term D, v.val = substitute (.cons u.val .nil) 0 body →
        Realizes (nativeTerms S) (wfOf S) D v (f x)) :
    Realizes (nativeTerms S) (wfOf S) (.arrow A D) ⟨.lam (actualType (nativeShape A)) body, hl⟩ f := by
  obtain ⟨wf', rule⟩ := NativeOrdinalRealizationProof.exact_NativeLambdaRealization S
  refine rule A D body hl f (fun x u hu => ?_)
  obtain ⟨result, resultValue, _, _⟩ :=
    NativeClosedBetaChecks.exact_ClosedNativeBeta S (actualType (nativeShape A))
      (actualType (nativeShape D)) body hl u
  exact ⟨result, resultValue, H x u hu result resultValue⟩

/-- The native iterator applied to realizers realizes the full-prefix orbit. -/
theorem iteratorApplied (S : Signature) (A : FiniteType) (α : CountableOrdinal)
    (i : (nativeTerms S).term .base) (hi : Realizes (nativeTerms S) (wfOf S) .base i α)
    (f : Value A → Value A) (P : (nativeTerms S).term (.arrow A A))
    (hP : Realizes (nativeTerms S) (wfOf S) (.arrow A A) P f)
    (x : Value A) (U : (nativeTerms S).term A) (hU : Realizes (nativeTerms S) (wfOf S) A U x) :
    ∃ c : (nativeTerms S).term A, c.val = applied (nativeShape A) i.val P.val U.val ∧
      Realizes (nativeTerms S) (wfOf S) A c (orbit A f x α) := by
  obtain ⟨wf', h⟩ := NativeOrdinalIterationProof.exact_NativeIteratorRealizesFullPrefix S
  obtain ⟨iterate, equations, realizes⟩ := h A
  have unique : (fun β => iterate β f x) = orbit A f x :=
    (exact_FullPrefixOrbitExists A f x).unique (equations f x) (orbitEquations A f x)
  have e : iterate α f x = orbit A f x α := congrFun unique α
  have h1 := realizes α i hi f P hP x U hU
  rw [e] at h1
  exact ⟨_, rfl, h1⟩

def zeroTerm (S : Signature) : (nativeTerms S).term .base := ⟨towerZero, zeroClosed S⟩

theorem zeroRealizes (S : Signature) : Realizes (nativeTerms S) (wfOf S) .base (zeroTerm S) zeroValue := by
  show (0 : Ordinal.{0}) ≤ ((wfOf S).apply (zeroTerm S)).rank
  exact not_lt.mp not_lt_zero

/-- Applying to the slots `m, …, 1` and then `Z`. -/
theorem natDownRealizes (S : Signature) (m : Nat) (a : Nat → Expr) (xs : Env)
    (ha : ∀ j, 1 ≤ j → j ≤ m → ∃ c : (nativeTerms S).term (tier j), c.val = a j ∧
      Realizes (nativeTerms S) (wfOf S) (tier j) c (xs j)) :
    ∀ (v : (nativeTerms S).term (tier (m+1))) (y : Value (tier (m+1))),
      Realizes (nativeTerms S) (wfOf S) (tier (m+1)) v y →
      ∃ c : (nativeTerms S).term .base, c.val = natDown m v.val a ∧
        Realizes (nativeTerms S) (wfOf S) .base c (semDown m y xs) := by
  induction m with
  | zero =>
    intro v y hv
    exact ⟨_, rfl, hv zeroValue (zeroTerm S) (zeroRealizes S)⟩
  | succ m ih =>
    intro v y hv
    obtain ⟨c, hc, hcr⟩ := ha (m+1) (by omega) le_rfl
    have hv' := hv (xs (m+1)) c hcr
    obtain ⟨d, hd, hdr⟩ := ih (fun j h1 h2 => ha j h1 (by omega)) _ _ hv'
    refine ⟨d, ?_, hdr⟩
    rw [hd]
    show natDown m (app (tierType (m+1)) (tierType (m+1)) v.val c.val) a = _
    rw [hc]
    rfl

/-- The (B_T) spine with closed slots and a closed realizer `i` for `α`. -/
theorem spineRealizes (S : Signature) (l : Nat) (α : CountableOrdinal)
    (i : (nativeTerms S).term .base) (hi : Realizes (nativeTerms S) (wfOf S) .base i α)
    (b : Nat → Expr) (xs : Env)
    (hb : ∀ j, 1 ≤ j → j ≤ l + 1 → ∃ c : (nativeTerms S).term (tier j), c.val = b j ∧
      Realizes (nativeTerms S) (wfOf S) (tier j) c (xs j)) :
    ∃ c : (nativeTerms S).term .base, c.val = spine l i.val b ∧
      Realizes (nativeTerms S) (wfOf S) .base c (spineValue l xs α) := by
  cases l with
  | zero =>
    obtain ⟨P, hP, hPr⟩ := hb 1 le_rfl le_rfl
    obtain ⟨c, hc, hcr⟩ := iteratorApplied S (tier 0) α i hi (xs 1) P hPr zeroValue (zeroTerm S)
      (zeroRealizes S)
    refine ⟨c, ?_, hcr⟩
    rw [hc, hP]
    rfl
  | succ m =>
    obtain ⟨P, hP, hPr⟩ := hb (m+2) (by omega) le_rfl
    obtain ⟨U, hU, hUr⟩ := hb (m+1) (by omega) (by omega)
    obtain ⟨c0, hc0, hc0r⟩ := iteratorApplied S (tier (m+1)) α i hi (xs (m+2)) P hPr (xs (m+1)) U hUr
    obtain ⟨c, hc, hcr⟩ := natDownRealizes S m b xs (fun j h1 h2 => hb j h1 (by omega)) c0 _ hc0r
    refine ⟨c, ?_, hcr⟩
    rw [hc, hc0, hP, hU]
    rfl

/-- Claim(k): with slots `≤ k` bound and slots `> k` closed realizers of `xs`, the partial
tower realizes the curried value over the remaining binders. -/
theorem partialRealizes (S : Signature) (F : (nativeTerms S).term (tier 2)) (φ : Value (tier 2))
    (hF : Realizes (nativeTerms S) (wfOf S) (tier 2) F φ) (l : Nat) :
    ∀ k, k ≤ l + 1 → ∀ (a : Nat → Expr) (xs : Env),
      (∀ j, 1 ≤ j → j ≤ k → a j = boundSlots j) →
      (∀ j, k < j → j ≤ l + 1 → ∃ c : (nativeTerms S).term (tier j), c.val = a j ∧
        Realizes (nativeTerms S) (wfOf S) (tier j) c (xs j)) →
      ∀ t : (nativeTerms S).term (tier (k+1)), t.val = binders k (fixBody F.val l a) →
        Realizes (nativeTerms S) (wfOf S) (tier (k+1)) t
          (curryEnv k (fun ys => φ (fun α => spineValue l ys α)) xs) := by
  intro k
  induction k with
  | zero =>
    intro _ a xs _ hc t ht
    have closedSlots : ∀ j, 1 ≤ j → j ≤ l + 1 → ClosedNative S (a j) (tierType j) := by
      intro j h1 h2
      obtain ⟨c, hcv, _⟩ := hc j (by omega) h2
      rw [← hcv]
      exact c.property
    let L : (nativeTerms S).term (tier 1) :=
      ⟨.lam indexType (spine l (.bound indexType 0) a), lambdaSpineClosed S l a closedSlots⟩
    have hL : Realizes (nativeTerms S) (wfOf S) (tier 1) L (fun α => spineValue l xs α) := by
      refine lambdaRule S .base .base (spine l (.bound indexType 0) a)
        (lambdaSpineClosed S l a closedSlots) _ (fun α i hi v hv => ?_)
      have hval : v.val = spine l i.val (fun j => substitute (.cons i.val .nil) 0 (a j)) := by
        rw [hv, substSpine S, atSlot i.property.1.1.1 0]
      obtain ⟨c, hcv, hcr⟩ := spineRealizes S l α i hi (fun j => substitute (.cons i.val .nil) 0 (a j)) xs
        (fun j h1 h2 => by
          obtain ⟨d, hdv, hdr⟩ := hc j (by omega) h2
          refine ⟨d, ?_, hdr⟩
          rw [← hdv, unchanged d.property.1.1.1])
      exact transfer (hval.trans hcv.symm) hcr
    have happ := hF _ L hL
    exact transfer ht happ
  | succ k ih =>
    intro hk a xs hb hc t ht
    have hl : ClosedNative S (.lam (tierType (k+1)) (binders k (fixBody F.val l a)))
        (.arrow (tierType (k+1)) (tierType (k+1))) := by
      have h := t.property
      rw [ht] at h
      exact h
    have e : t = ⟨.lam (tierType (k+1)) (binders k (fixBody F.val l a)), hl⟩ := Subtype.ext ht
    rw [e]
    refine lambdaRule S (tier (k+1)) (tier (k+1)) (binders k (fixBody F.val l a)) hl _
      (fun x u hu v hv => ?_)
    have hval : v.val = binders k (fixBody F.val l
        (fun j => substitute (.cons u.val .nil) (0 + k + 1) (a j))) := by
      rw [hv, substBinders, substFixBody S F.property]
    refine ih (by omega) (fun j => substitute (.cons u.val .nil) (0 + k + 1) (a j))
      (Function.update xs (k+1) x) (fun j h1 h2 => ?_) (fun j h1 h2 => ?_) v hval
    · show substitute (.cons u.val .nil) (0 + k + 1) (a j) = boundSlots j
      rw [hb j h1 (by omega)]
      exact nearer _ _ j _ (by omega)
    · by_cases hj : j = k + 1
      · subst hj
        refine ⟨u, ?_, ?_⟩
        · show u.val = substitute (.cons u.val .nil) (0 + k + 1) (a (k+1))
          rw [hb (k+1) (by omega) le_rfl, Nat.zero_add]
          exact (atSlot u.property.1.1.1 (k+1)).symm
        · rw [Function.update_self]
          exact hu
      · obtain ⟨c, hcv, hcr⟩ := hc j (by omega) h2
        refine ⟨c, ?_, ?_⟩
        · show c.val = substitute (.cons u.val .nil) (0 + k + 1) (a j)
          rw [← hcv, unchanged c.property.1.1.1]
        · rw [Function.update_of_ne hj]
          exact hcr

theorem exact_NativeTowerRealization : NativeTowerRealization := by
  intro S
  refine ⟨wfOf S, ?_⟩
  intro F φ hF l
  refine ⟨⟨towerTerm F.val l, towerClosed S F.property l⟩, rfl, ?_⟩
  exact partialRealizes S F φ hF l (l+1) le_rfl boundSlots (fun j => valueDefault (tier j))
    (fun _ _ _ => rfl) (fun j h1 h2 => by omega) _ rfl

/-! Faithfulness checks against the printed (B), (B_T) at the first levels. -/

theorem towerTerm_zero (F : Expr) :
    towerTerm F 0 = .lam (tierType 1) (app (tierType 1) (tierType 1) F
      (.lam indexType (applied (nativeShape .base) (.bound indexType 0) (.bound (tierType 1) 1) towerZero))) :=
  rfl

theorem towerTerm_one (F : Expr) :
    towerTerm F 1 = .lam (tierType 2) (.lam (tierType 1) (app (tierType 1) (tierType 1) F
      (.lam indexType (app indexType indexType
        (applied (nativeShape (tier 1)) (.bound indexType 0) (.bound (tierType 2) 2) (.bound (tierType 1) 1))
        towerZero)))) :=
  rfl

theorem towerValue_zero (φ : Value (tier 2)) (h : Value (tier 1)) :
    towerValue φ 0 h = φ (fun α => orbit (tier 0) h zeroValue α) := by
  simp [towerValue, curryEnv, spineValue]

theorem towerValue_one (φ : Value (tier 2)) (h : Value (tier 2)) (h₁ : Value (tier 1)) :
    towerValue φ 1 h h₁ = φ (fun α => orbit (tier 1) h h₁ α zeroValue) := by
  simp [towerValue, curryEnv, spineValue, semDown]

#print axioms exact_NativeTowerRealization

end LogicLineages.PersistentMarking.NativeTowerProof
