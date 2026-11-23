module

public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalIterationTargets
public import LogicLineages.PersistentMarking.OrdinalNativeOrbitProof

@[expose] public section

/-! # The finite-type extractor towers (B), (B_T) of Paper 16, ordinals.tex 531–550

Printed: `A_0 = ι`, `A_{l+1} = A_l → A_l`, and
`B_l h h_l ⋯ h_1 = Fix(λα. h^α h_l ⋯ h_1 0)` with `B_l : A_{l+2}`.
Its native realizer is `λh.λh_l⋯λh_1. fix (λα:σ. (It_{A_l} α h h_l) h_{l-1} ⋯ h_1 Z)`,
whose inner body for `l = 0` is `It_ι α h Z`. "Prefix the corresponding typed lambdas and use
fix for Fix. The terminal Z is present in every case."

Here `Fix` is the semantic value `φ` realized by the supplied fix term `F`; the printed fix
(`λf z. It w f (s z)`, realizing `f^ω(ζ+1)`) is one instance. `h^α x` is the full-prefix orbit
`orbit A_l h x α` of convention (I), and `0` is the countable ordinal zero. Nothing here depends on
Simmons's helpfulness, the Veblen-hull collapse, ψ_B or BH.

De Bruijn layout of the body under `λα`: `α` is index 0, `h_j` is index `j` (`1 ≤ j ≤ l`), `h` is
index `l+1`. A slot function `a : Nat → Expr` gives the term at each index `1..l+1`; the printed
term uses `a j = .bound |A_j| j`. -/

namespace LogicLineages.PersistentMarking.NativeTowerTargets
open Spine NativeReduction NativeIndexedCarrierTargets NativeIteratorTargets NativeIteratorStrictTargets
open OrdinalRealizationTargets NativeOrdinalRealizationTargets NativeOrdinalIterationTargets
open OrdinalNativeOrbitProof

/-- `A_0 = ι`, `A_{l+1} = A_l → A_l`. -/
def tier : Nat → FiniteType
  | 0 => .base
  | l + 1 => .arrow (tier l) (tier l)

/-- The actual type `|A_l|` (`|ι| = σ = o → o`). -/
abbrev tierType (l : Nat) : Ty := actualType (nativeShape (tier l))

/-- `Z = λz:o.z : σ`. -/
def towerZero : Expr := .lam .ground (.bound .ground 0)

/-- Apply `v : |A_{m+1}|` to the slots `m, m-1, …, 1` and then to `Z`. -/
def natDown : Nat → Expr → (Nat → Expr) → Expr
  | 0, v, _ => app indexType indexType v towerZero
  | m + 1, v, a => natDown m (app (tierType (m+1)) (tierType (m+1)) v (a (m+1))) a

/-- The (B_T) spine under `λα` with `α := alpha`: `It_ι α h Z` for `l = 0`, and
`(It_{A_l} α h h_l) h_{l-1} ⋯ h_1 Z` for `l ≥ 1`; `h = a (l+1)`, `h_j = a j`. -/
def spine : Nat → Expr → (Nat → Expr) → Expr
  | 0, alpha, a => applied (nativeShape (tier 0)) alpha (a 1) towerZero
  | m + 1, alpha, a => natDown m (applied (nativeShape (tier (m+1))) alpha (a (m+2)) (a (m+1))) a

/-- `λh_k:|A_k|. ⋯ λh_1:|A_1|. X` (outermost binder has slot `k`). -/
def binders : Nat → Expr → Expr
  | 0, X => X
  | k + 1, X => .lam (tierType (k+1)) (binders k X)

/-- The fix application with the spine abstracted over `α`. -/
def fixBody (F : Expr) (l : Nat) (a : Nat → Expr) : Expr :=
  app (tierType 1) (tierType 1) F (.lam indexType (spine l (.bound indexType 0) a))

/-- Printed slot layout: `h_j` and `h` are the bound variables. -/
def boundSlots (j : Nat) : Expr := .bound (tierType j) j

/-- The native realizer of `B_l`: `λh:|A_{l+1}|. λh_l ⋯ λh_1. F (λα:σ. spine)`. -/
def towerTerm (F : Expr) (l : Nat) : Expr := binders (l+1) (fixBody F l boundSlots)

/-! Semantic side. -/

/-- The countable ordinal zero. -/
def zeroValue : CountableOrdinal :=
  ⟨0, ⟨⟨fun _ => 0, fun b _ _ => (not_lt_zero b.property).elim⟩⟩⟩

/-- An arbitrary default value (only used for unread environment slots). -/
def valueDefault : (A : FiniteType) → Value A
  | .base => zeroValue
  | .arrow _ D => fun _ => valueDefault D

/-- Environments: slot `j` holds a value of type `A_j`. -/
abbrev Env := (j : Nat) → Value (tier j)

/-- Apply `v : A_{m+1}` to `xs m, …, xs 1` and then to `0`. -/
def semDown : (m : Nat) → Value (tier (m+1)) → Env → CountableOrdinal
  | 0, v, _ => v zeroValue
  | m + 1, v, xs => semDown m (v (xs (m+1))) xs

/-- `h^α h_l ⋯ h_1 0` with `h = xs (l+1)`, `h_j = xs j`, `h^α x = orbit A_l h x α`. -/
noncomputable def spineValue : (l : Nat) → Env → CountableOrdinal → CountableOrdinal
  | 0, xs, α => orbit (tier 0) (xs 1) zeroValue α
  | m + 1, xs, α => semDown m (orbit (tier (m+1)) (xs (m+2)) (xs (m+1)) α) xs

/-- Curry the binders `k, k-1, …, 1` into the environment. -/
def curryEnv : (k : Nat) → (Env → Value (tier 1)) → Env → Value (tier (k+1))
  | 0, G, xs => G xs
  | k + 1, G, xs => fun x => curryEnv k G (Function.update xs (k+1) x)

/-- `B_l = λh h_l ⋯ h_1. Fix(λα. h^α h_l ⋯ h_1 0)` with `Fix := φ`. -/
noncomputable def towerValue (φ : Value (tier 2)) (l : Nat) : Value (tier (l+2)) :=
  curryEnv (l+1) (fun xs => φ (fun α => spineValue l xs α)) (fun j => valueDefault (tier j))

/-- Every `B_l` is realized by its printed native term, for any closed native fix term `F`
realizing the semantic `Fix` value `φ`. -/
def NativeTowerRealization : Prop :=
  ∀ S, ∃ wf : WellFounded (@NativeBelow S indexType),
    ∀ (F : (nativeTerms S).term (tier 2)) (φ : Value (tier 2)),
      Realizes (nativeTerms S) wf (tier 2) F φ →
      ∀ l, ∃ t : (nativeTerms S).term (tier (l+2)),
        t.val = towerTerm F.val l ∧ Realizes (nativeTerms S) wf (tier (l+2)) t (towerValue φ l)

end LogicLineages.PersistentMarking.NativeTowerTargets
