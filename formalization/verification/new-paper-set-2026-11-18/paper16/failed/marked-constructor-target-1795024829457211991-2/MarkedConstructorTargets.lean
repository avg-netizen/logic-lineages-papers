import LogicLineages.PersistentMarking.MarkedConstructorValue
import LogicLineages.PersistentMarking.HereditaryOrderTargets
namespace LogicLineages.PersistentMarking.MarkedConstructorTargets
open Spine NameBridge DecisionPorts FiniteDomainFoundation HereditaryDomainCode HereditaryDomainSemantics
open MarkedFamilyParameters (Parameter)

inductive Delete (x : Expr) : List Expr → List Expr → Prop where
  | here : Delete x (x::xs) xs
  | there : Delete x xs ys → Delete x (y::xs) (y::ys)
inductive SplitList {α : Type} : List α → List α → List α → Prop where
  | nil : SplitList [] [] []
  | left : SplitList xs ys zs → SplitList (x::xs) (x::ys) zs
  | right : SplitList xs ys zs → SplitList (x::xs) ys (x::zs)
inductive Matches (E : Environment) (Γ : Context) : List MarkedExtras.Tagged → List Expr → Prop where
  | nil : Matches E Γ [] []
  | cons : Delete t ts rest → MarkedConstructorTests.bit false E Γ a t = true →
      Matches E Γ bs rest → Matches E Γ (a::bs) ts

def Replaces (E : Environment) (Γ : Context) (bs : List MarkedExtras.Tagged) (ts : List Expr) : Prop :=
  ∃ kept removed matched added, SplitList bs kept removed ∧ SplitList ts matched added ∧
    removed ≠ [] ∧ Matches E Γ kept matched ∧
    ∀ t, t ∈ added → ∃ a, a ∈ removed ∧ MarkedConstructorTests.bit true E Γ a t = true

def WholeWitness (E : Environment) (heads : List Head) (M : Code) (p : Parameter) (ts : List Expr) : Prop :=
  ∀ t, t ∈ ts → ∃ c, MarkedConstructorTests.owner E heads M p t.type = some c ∧
    (HereditaryDomainSemantics.decode E t.type p.2.2.1 c).weak p.2.2.1 t = true

def SelectWitness (E : Environment) (heads : List Head) (M : Code) (p : Parameter) (t : Expr) : Prop :=
  ∃ a, a ∈ p.1.arguments.zip p.2.2.2.1 ++ p.2.2.2.2 ∧
    ((a.1=p.2.1 ∧ MarkedConstructorTests.bit false E p.2.2.1 a t = true) ∨
     ∃ ds xs, (ds,p.2.1) ∈ fullPrefixes a.1 ∧
       MarkedConstructorTests.ownerTuple E heads M p ds = some xs ∧
       (HereditaryDomainSemantics.decode E p.2.1 p.2.2.1
         (StructuralActions.fullAction E a.1 p.2.2.1 a.2 ds p.2.1 xs)).weak p.2.2.1 t = true)

def FAbsWitness (E : Environment) (heads : List Head) (M : Code) (p : Parameter) (t : Expr) : Prop :=
  ∃ σ τ body i c, p.2.1 = .arrow σ τ ∧ t = .lam σ body ∧
    ProtectedSpineEnvironment.openingSlot p.2.2.1 = some i ∧
    StructuralActions.markedAction E heads M (MarkedConstructorTests.fabsParameter E p σ τ i) = some c ∧
    (HereditaryDomainSemantics.decode E τ (ProtectedSpineEnvironment.openingContext p.2.2.1 σ i) c).weak
      (ProtectedSpineEnvironment.openingContext p.2.2.1 σ i) (openBody σ (portName E.names i) body) = true

/-- Local inventory interface; actual source K must discharge it, not assume a new carrier law. -/
def PrefixClosed (E : Environment) : Prop := ∀ σ, σ ∈ E.types → ∀ ds τ,
  (ds,τ) ∈ fullPrefixes σ → τ ∈ E.types ∧ ∀ ρ, ρ ∈ ds → ρ ∈ E.types

def MatchingExact : Prop := ∀ E Γ bs ts,
  MarkedConstructorTests.matching E Γ bs ts = true ↔ Matches E Γ bs ts

def MultisetExact : Prop := ∀ E Γ bs ts,
  MarkedConstructorTests.multiset E Γ bs ts = true ↔ Replaces E Γ bs ts

def SelectExact : Prop := ∀ E heads M p t,
  MarkedConstructorTests.selectTest E heads M p t = true ↔ SelectWitness E heads M p t

def CopyExact : Prop := ∀ S E heads M p t,
  MarkedConstructorTests.copyTest S E heads M p t = true ↔
    ∃ g ts, t = .head g ts ∧ g.result=p.2.1 ∧ Precedes S p.1 g ∧
      WholeWitness E heads M p (MarkedConstructorTests.terms ts)

def StatExact : Prop := ∀ S E heads M p t,
  MarkedConstructorTests.statTest S E heads M p t = true ↔
    ∃ g ts, t = .head g ts ∧ g.result=p.2.1 ∧ Equivalent S p.1 g ∧
      Replaces E p.2.2.1 (p.1.arguments.zip p.2.2.2.1) (MarkedConstructorTests.terms ts) ∧
      WholeWitness E heads M p (MarkedConstructorTests.terms ts)

def FAbsExact : Prop := ∀ E heads M p t,
  MarkedConstructorTests.fabsTest E heads M p t = true ↔ FAbsWitness E heads M p t

def Fields : Prop := ∀ S E heads M p Δ t,
  (MarkedConstructorValue.build S E heads M p).available Δ = true ∧
  (MarkedConstructorValue.build S E heads M p).strict Δ t =
    (MarkedConstructorValue.build S E heads M p).weak Δ t ∧
  ((MarkedConstructorValue.build S E heads M p).weak Δ t = true ↔
    SelectWitness E heads M (MarkedFamilyCoherence.weakenParameter E p Δ) t ∨
    MarkedConstructorTests.copyTest S E heads M (MarkedFamilyCoherence.weakenParameter E p Δ) t = true ∨
    MarkedConstructorTests.statTest S E heads M (MarkedFamilyCoherence.weakenParameter E p Δ) t = true ∨
    FAbsWitness E heads M (MarkedFamilyCoherence.weakenParameter E p Δ) t)

def TupleSuccess : Prop := ∀ S E heads M p Δ ds τ xs,
  PrefixClosed E → M ∈ MarkedFamilyCoherence.retained E heads → MarkedFamilyParameters.Valid E heads p →
  WellFormed E.types E.ports Δ → Extends p.2.2.1 Δ → (ds,τ) ∈ fullPrefixes p.2.1 → TupleValues E Δ ds xs →
  ∃ c, StructuralActions.markedAction E heads M
    (p.1,τ,Δ,(MarkedFamilyCoherence.weakenParameter E p Δ).2.2.2.1,
      StructuralActions.insertExtras E Δ (MarkedFamilyCoherence.weakenParameter E p Δ).2.2.2.2 (ds.zip xs)) = some c ∧
    c ∈ (descriptor E τ).carriers Δ ∧ (MarkedConstructorValue.build S E heads M p).application Δ ds τ xs = c

def ValueValid : Prop := ∀ S E heads M p,
  PrefixClosed E → M ∈ MarkedFamilyCoherence.retained E heads → MarkedFamilyParameters.Valid E heads p →
  HereditaryDomainSemantics.Valid E p.2.1 p.2.2.1 (MarkedConstructorValue.build S E heads M p)

def InputMonotone : Prop := ∀ S E heads M p q,
  PrefixClosed E → M ∈ MarkedFamilyCoherence.retained E heads →
  MarkedFamilyParameters.Valid E heads p → MarkedFamilyParameters.Valid E heads q →
  MarkedFamilyCoherence.InputLE E p q →
  HereditaryOrderTargets.SemanticLE E p.2.1 p.2.2.1
    (MarkedConstructorValue.build S E heads M p) (MarkedConstructorValue.build S E heads M q)

def Coherent : Prop := ∀ S E heads M p Δ,
  PrefixClosed E → M ∈ MarkedFamilyCoherence.retained E heads → MarkedFamilyParameters.Valid E heads p →
  WellFormed E.types E.ports Δ → Extends p.2.2.1 Δ →
  ValueEq E p.2.1 Δ (MarkedConstructorValue.build S E heads M p)
    (MarkedConstructorValue.build S E heads M (MarkedFamilyCoherence.weakenParameter E p Δ))

def FamilyMonotone : Prop := ∀ S E heads M N p,
  PrefixClosed E → M ∈ MarkedFamilyCoherence.retained E heads → N ∈ MarkedFamilyCoherence.retained E heads →
  MarkedFamilyParameters.Valid E heads p → MarkedFamilyLattice.le E heads M N = true →
  HereditaryOrderTargets.SemanticLE E p.2.1 p.2.2.1
    (MarkedConstructorValue.build S E heads M p) (MarkedConstructorValue.build S E heads N p)
end LogicLineages.PersistentMarking.MarkedConstructorTargets
