module

public import LogicLineages.ComputabilityKnowledge.GorbowSupportCode

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowSupportCode
open GorbowSyntax GorbowSyntaxValidation GorbowFreeSupport
open LogicLineages.ComputabilityKnowledge.GorbowSupportCode

def ScannerInvariant : Prop :=
  (∀ (n : Nat) (t : Term n) (i : Fin n) (tasks : List Task) (b : Bool),
    (GorbowTermPrefixCode.encode t).foldl (observeStep (n-i.val)) (some ((0,n)::tasks),b) =
      (some tasks,b || t.uses i)) ∧
  (∀ (n : Nat) (φ : Formula n) (i : Fin n) (tasks : List Task) (b : Bool),
    (GorbowFormulaPrefixCode.encode φ).foldl (observeStep (n-i.val)) (some ((1,n)::tasks),b) =
      (some tasks,b || φ.uses i))

def ExactNames : Prop :=
  (∀ n raw names, termNames n raw = some names ↔ ∃ t : Term n,
    raw = GorbowTermPrefixCode.encode t ∧ names = (List.range n).filter (fun i => decide (i ∈ termSupport t))) ∧
  (∀ n raw names, formulaNames n raw = some names ↔ ∃ φ : Formula n,
    raw = GorbowFormulaPrefixCode.encode φ ∧ names = (List.range n).filter (fun i => decide (i ∈ formulaSupport φ)))

def ExactRejection : Prop :=
  (∀ n raw, termNames n raw = none ↔ GorbowTermPrefixCode.decode n raw = none) ∧
  (∀ n raw, formulaNames n raw = none ↔ GorbowFormulaPrefixCode.decode n raw = none)

def ExactSelector : Prop := ∀ raw, selectorCode raw = true ↔
  ∃ A : Selector, raw = GorbowFormulaPrefixCode.encode A.val

def ExactPreciseArity : Prop :=
  (∀ m n raw, preciseTermCode m n raw = true ↔ ∃ t : Term m,
    raw = GorbowTermPrefixCode.encode t ∧ (termSupport t).card = n) ∧
  (∀ m n raw, preciseFormulaCode m n raw = true ↔ ∃ φ : Formula m,
    raw = GorbowFormulaPrefixCode.encode φ ∧ PreciselyFree n φ)

def UniformPrograms : Prop :=
  Primrec (fun p : Nat × State × Nat => sees p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × ObservedState × Nat => observeStep p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × Nat × List Nat => occurs p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec (fun p : Nat × List Nat => termNames p.1 p.2) ∧
  Primrec (fun p : Nat × List Nat => formulaNames p.1 p.2) ∧
  Primrec selectorCode ∧
  Primrec (fun p : Nat × Nat × List Nat => preciseTermCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × List Nat => preciseFormulaCode p.1 p.2.1 p.2.2)

def Target : Prop := ScannerInvariant ∧ ExactNames ∧ ExactRejection ∧ ExactSelector ∧ ExactPreciseArity ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowSupportCode
