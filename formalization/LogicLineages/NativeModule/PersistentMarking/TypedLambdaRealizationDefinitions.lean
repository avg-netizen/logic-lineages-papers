module

public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalRealizationTargets
public import LogicLineages.NativeModule.PersistentMarking.NativeTowerSyntaxProof

@[expose] public section

namespace LogicLineages.PersistentMarking.TypedLambdaRealization
open Spine NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets NativeIteratorStrictTargets
open OrdinalRealizationTargets NativeOrdinalRealizationTargets

abbrev nativeType (A : FiniteType) : Ty := actualType (nativeShape A)

/-- Intrinsically typed de Bruijn variables; the first context entry is nearest. -/
inductive Var : List FiniteType → FiniteType → Type where
  | here {Γ A} : Var (A :: Γ) A
  | there {Γ A B} : Var Γ A → Var (B :: Γ) A

/-- The full simply typed lambda/application grammar over the existing semantic
finite types. Constants are an arbitrary separately interpreted family. -/
inductive Term (C : FiniteType → Type) : List FiniteType → FiniteType → Type where
  | var {Γ A} : Var Γ A → Term C Γ A
  | constant {Γ A} : C A → Term C Γ A
  | app {Γ A D} : Term C Γ (.arrow A D) → Term C Γ A → Term C Γ D
  | lam {Γ A D} : Term C (A :: Γ) D → Term C Γ (.arrow A D)

abbrev ConstantTerms (S : Signature) (C : FiniteType → Type) :=
  (A : FiniteType) → C A → (nativeTerms S).term A
abbrev ConstantValues (C : FiniteType → Type) := (A : FiniteType) → C A → Value A
abbrev TermEnv (S : Signature) (Γ : List FiniteType) :=
  (A : FiniteType) → Var Γ A → (nativeTerms S).term A
abbrev ValueEnv (Γ : List FiniteType) := (A : FiniteType) → Var Γ A → Value A

/-- A local bound occurrence or an actual closed native term. Binder lifting
changes only bound indices; a closed native term is inserted literally. -/
inductive Entry (S : Signature) (A : FiniteType) where
  | bound (index : Nat)
  | closed (term : (nativeTerms S).term A)

abbrev EntryEnv (S : Signature) (Γ : List FiniteType) :=
  (A : FiniteType) → Var Γ A → Entry S A

def entryExpr {S A} : Entry S A → Expr
  | .bound i => .bound (nativeType A) i
  | .closed q => q.val

def liftEntry {S A} : Entry S A → Entry S A
  | .bound i => .bound (i+1)
  | .closed q => .closed q

def liftEntries {S Γ A} (ρ : EntryEnv S Γ) : EntryEnv S (A :: Γ) :=
  fun B v => match v with
    | .here => .bound 0
    | .there w => liftEntry (ρ B w)

def closedEntries {S Γ} (ρ : TermEnv S Γ) : EntryEnv S Γ := fun A v => .closed (ρ A v)

def extendTerms {S Γ A} (u : (nativeTerms S).term A) (ρ : TermEnv S Γ) : TermEnv S (A :: Γ) :=
  fun B v => match v with
    | .here => u
    | .there w => ρ B w

def extendValues {Γ A} (x : Value A) (η : ValueEnv Γ) : ValueEnv (A :: Γ) :=
  fun B v => match v with
    | .here => x
    | .there w => η B w

/-- Literal compilation into the existing native syntax: no beta normalization,
semantic evaluation, choice of representative, or fresh auxiliary head. -/
def compile {S C} (c : ConstantTerms S C) :
    {Γ : List FiniteType} → {A : FiniteType} → Term C Γ A → EntryEnv S Γ → Expr
  | _, _, .var v, ρ => entryExpr (ρ _ v)
  | _, _, .constant a, _ => (c _ a).val
  | _, _, @Term.app _ _ A D f u, ρ =>
      NativeReduction.app (nativeType A) (nativeType D) (compile c f ρ) (compile c u ρ)
  | _, _, @Term.lam _ _ A _ body, ρ =>
      .lam (nativeType A) (compile c body (liftEntries ρ))

/-- Ordinary set-function interpretation, using the repository's full `Value`
spaces. No monotonicity restriction is imposed at arrow types. -/
def evaluate {C} (c : ConstantValues C) :
    {Γ : List FiniteType} → {A : FiniteType} → Term C Γ A → ValueEnv Γ → Value A
  | _, _, .var v, η => η _ v
  | _, _, .constant a, _ => c _ a
  | _, _, .app f u, η => evaluate c f η (evaluate c u η)
  | _, _, .lam body, η => fun x => evaluate c body (extendValues x η)

def EntryFits {S A} (Δ : BoundContext) : Entry S A → Prop
  | .bound i => Δ i = some (nativeType A)
  | .closed _ => True

def EnvFits {S Γ} (Δ : BoundContext) (ρ : EntryEnv S Γ) : Prop :=
  ∀ A v, EntryFits Δ (ρ A v)

/-- Exact one-binder closing relation on entries at an arbitrary depth. Its hit
case carries the real closed native argument, not a semantic/body premise. -/
inductive EntrySub {S A} (u : (nativeTerms S).term A) (depth : Nat) :
    {B : FiniteType} → Entry S B → Entry S B → Prop where
  | below {B} (i : Nat) (hi : i < depth) :
      EntrySub u depth (Entry.bound (A := B) i) (.bound i)
  | hit : EntrySub u depth (.bound depth) (.closed u)
  | above {B} (i : Nat) (hi : depth < i) :
      EntrySub u depth (Entry.bound (A := B) i) (.bound (i-1))
  | closed {B} (q : (nativeTerms S).term B) : EntrySub u depth (.closed q) (.closed q)

def EnvSub {S Γ A} (u : (nativeTerms S).term A) (depth : Nat)
    (ρ σ : EntryEnv S Γ) : Prop := ∀ B v, EntrySub u depth (ρ B v) (σ B v)

def emptyConstants (S : Signature) : ConstantTerms S (fun _ => Empty) := fun _ e => nomatch e
def emptyConstantValues : ConstantValues (fun _ => Empty) := fun _ e => nomatch e
def emptyEntries (S : Signature) : EntryEnv S [] := fun _ v => nomatch v
def emptyTerms (S : Signature) : TermEnv S [] := fun _ v => nomatch v
def emptyValues : ValueEnv [] := fun _ v => nomatch v

end LogicLineages.PersistentMarking.TypedLambdaRealization
