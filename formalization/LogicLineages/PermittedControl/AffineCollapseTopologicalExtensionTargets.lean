module
public import LogicLineages.PermittedControl.AffineCollapsePairListLowTargets

@[expose] public section
namespace LogicLineages.PermittedControl.AffineCollapseTopologicalExtension
open OrdinalComparison
open AffineCollapsePairListLow (Pair GraphsAt)

abbrev Valuation := Nat → Nat

def input (p : Pair) : Nat := p.2.2.1
def output (p : Pair) : Nat := p.2.2.2

def born : List Pair → List Nat
  | [] => []
  | p :: ps => input p :: output p :: born ps

def Topological : List Nat → List Pair → Prop
  | _, [] => True
  | known, p :: ps =>
    input p ≠ output p ∧ input p ∉ known ∧ output p ∉ known ∧
      (∀ t ∈ p.2.1.2, t.2 ∈ known) ∧ Topological (input p :: output p :: known) ps

def AgreesOutside (pairs : List Pair) (base final : Valuation) : Prop :=
  ∀ n : Nat, n ∉ born pairs → final n = base n

def graphAt (f : Nat → Nat) (p : Pair) (θ : Valuation) : Prop :=
  AffineCollapseGraphComposition.graph f (rawNoteEncode p.1.1) p.2.1 (input p) (output p) θ

def domainAt (p : Pair) (θ : Valuation) : Prop :=
  AffineCollapseGraphComposition.originalDomain (rawNoteEncode p.1.1) p.2.1 θ

noncomputable def valuesAt (f : Nat → Nat) (p : Pair) (θ : Valuation) : Nat × Nat :=
  AffineCollapseGraphComposition.originalValues f (rawNoteEncode p.1.1) p.2.1 θ

def put (p : Pair) (θ : Valuation) (values : Nat × Nat) : Valuation :=
  AffineCollapseGraphComposition.insertValues θ (input p) (output p) values

/-- Actual domain is tested at each intermediate valuation, then the
original two values are installed together. This is a semantic evaluator,
not a claim of finite-code circuit parsing or effectivity. -/
noncomputable def run (f : Nat → Nat) (θ : Valuation) : List Pair → Option Valuation
  | [] => some θ
  | p :: ps => @ite (Option Valuation) (domainAt p θ) (Classical.propDecidable _)
      (run f (put p θ (valuesAt f p θ)) ps) none

def ExactTopologicalExtension : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (known : List Nat) (pairs : List Pair), Topological known pairs →
      ∀ (base final : Valuation),
        run f base pairs = some final ↔ GraphsAt f final pairs ∧ AgreesOutside pairs base final

def UniqueTopologicalExtension : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (known : List Nat) (pairs : List Pair), Topological known pairs →
      ∀ base : Valuation,
        (run f base pairs ≠ none ↔
          ∃! final : Valuation, GraphsAt f final pairs ∧ AgreesOutside pairs base final) ∧
        ∀ final : Valuation, run f base pairs = some final →
          ∀ n ∈ known, final n = base n

def FullAffineCollapseTopologicalExtension : Prop :=
  ExactTopologicalExtension ∧ UniqueTopologicalExtension

end LogicLineages.PermittedControl.AffineCollapseTopologicalExtension
