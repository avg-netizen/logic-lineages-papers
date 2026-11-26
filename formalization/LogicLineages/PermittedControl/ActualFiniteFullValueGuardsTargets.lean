module
public import LogicLineages.PermittedControl.ActualFullLabelPairGuardsTargets
public import LogicLineages.PermittedControl.ActualPreparedSlotAppendTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFiniteFullValueGuards
open OrdinalComparison FieldComparison PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open ActualFullValueLabels (Label)
open ActualFullLabelPairGuards (Pair Answer choices cost Ready PaidUpdate ActualOutcome packet)
open ActualPreparedSlotAppend (Packet append)

def pairs (ls : List Label) : List Pair := ls.flatMap fun l => ls.map (fun r => (l,r))

/-- Literal pair occurrences are kept in lexicographic list-position
order. Inconsistent candidate answers are allowed syntactically, but
cannot satisfy the exact positive conjunction. -/
def patterns : Nat → List (List Answer)
  | 0 => [[]]
  | n+1 => choices.flatMap (fun a => (patterns n).map (List.cons a))

def compile (top : Nat) : List Pair → List Answer → Packet
  | [],[] => ([],.truth)
  | p::ps,a::as => append (packet top p a) (compile top ps as)
  | _,_ => ([],.falsity)

def familyCost (B : Nat) (ls : List Label) : Nat :=
  (pairs ls).foldr (fun p n => max (cost B p) n) 0

def ReadyFamily (B : Nat) (ρ : Nat → Nat) (top : Nat) (ls : List Label) : Prop :=
  (∀ l ∈ ls, l.rank ≤ top ∧ ProperField l.field) ∧
  ∀ l ∈ ls, l.rank < top → familyCost B ls ≤ ρ l.rank

def PaidFamily (B : Nat) (ρ : Nat → Nat) (top z : Nat) (ls : List Label) : Prop :=
  familyCost B ls ≤ z ∧ ∀ l ∈ ls, l.rank < top → ρ l.rank < z

def Matches (f θ : Nat → Nat) (ps : List Pair) (as : List Answer) : Prop :=
  List.Forall₂ (ActualOutcome f θ) ps as

def ExactFinitePatternEnumeration : Prop :=
  ∀ n : Nat, ∀ as : List Answer, as ∈ patterns n ↔ as.length = n

def ExactOrderedGuardFold : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (top : Nat) (ps : List Pair) (as : List Answer),
    as.length = ps.length →
    (∀ p ∈ ps, Ready B ρ top p) →
    let q := compile top ps as
    PreparedInput q.1 q.2 ∧
    (∃ ν : Nat → Nat, PreparedTableTied f top ρ q.1 ν) ∧
    ∀ (ν : Nat → Nat), PreparedTableTied f top ρ q.1 ν →
      ∀ z : Nat, (∀ p ∈ ps, PaidUpdate B ρ top z p) →
        (q.2.eval (Function.update ν 0 z) ↔ Matches f (Function.update ρ top z) ps as)

def ExactFiniteFullValueGuards : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (top : Nat) (ls : List Label), ReadyFamily B ρ top ls →
    (∀ as ∈ patterns (pairs ls).length,
      let q := compile top (pairs ls) as
      PreparedInput q.1 q.2 ∧
      (∃ ν : Nat → Nat, PreparedTableTied f top ρ q.1 ν) ∧
      ∀ (ν : Nat → Nat), PreparedTableTied f top ρ q.1 ν →
        ∀ z : Nat, PaidFamily B ρ top z ls →
          (q.2.eval (Function.update ν 0 z) ↔ Matches f (Function.update ρ top z) (pairs ls) as)) ∧
    ∀ z : Nat, PaidFamily B ρ top z ls →
      ∃ as ∈ patterns (pairs ls).length,
        Matches f (Function.update ρ top z) (pairs ls) as ∧
        ∃ ν : Nat → Nat, PreparedTableTied f top ρ (compile top (pairs ls) as).1 ν ∧
          ((compile top (pairs ls) as).2.eval (Function.update ν 0 z))

def FullActualFiniteFullValueGuards : Prop :=
  ExactFinitePatternEnumeration ∧ ExactOrderedGuardFold ∧ ExactFiniteFullValueGuards

end LogicLineages.PermittedControl.ActualFiniteFullValueGuards
