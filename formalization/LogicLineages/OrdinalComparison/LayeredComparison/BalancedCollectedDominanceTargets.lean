module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedCollectedDominanceDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineSyntaxDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.CollectedDominance.Targets

/-- Start with the ORIGINAL uncollected row at its ORIGINAL threshold. Equal
keys, zero coefficients, minimum-input witnesses and maximum-key witnesses are
not premises. Cancellation keeps the entire outside remainder; otherwise a
greatest actual surviving key exists and its nonzero coefficient gives the sign. -/
def ActualCollectedDichotomy : Prop := ∀ (basis : List Nat) (row : Row),
  wellFormed basis row → genuineHeads row →
  (∀ a ∈ row.atoms, threshold row ≤ input basis a.2) →
  ((Collection.collect basis row).atoms = [] ∧ value basis row = remainderValue basis row) ∨
    ∃ winner : Int × Atom, GreatestSurvivor basis row winner ∧
      winner.1 ≠ 0 ∧ Int.sign (value basis row) = Int.sign winner.1

/-- Every greatest surviving actual key gives the sign of the ORIGINAL row.
Its nonzero coefficient, distinct collected support and necessary finite
extrema are conclusions or internal proof obligations, never assumptions. -/
def EveryGreatestSurvivorSign : Prop := ∀ (basis : List Nat) (row : Row),
  wellFormed basis row → genuineHeads row →
  (∀ a ∈ row.atoms, threshold row ≤ input basis a.2) →
  ∀ winner : Int × Atom, GreatestSurvivor basis row winner →
    winner.1 ≠ 0 ∧ Int.sign (value basis row) = Int.sign winner.1

/-- Literal source expressions use ONE certificate, ONE actual basis and ONE
raw valuation throughout. The large branch is tested on the ORIGINAL signed
pair, before collection. Total cancellation gives two actual preceding-level
lowerPart terms; every greatest surviving key otherwise gives the source sign.
No independently ranging replacement basis is assumed. -/
def ActualSourceDichotomy : Prop := ∀ (k : Nat) (Γ : List Nat)
  (C : BalancedSyntax.Certificate (k::Γ)) (E F : BalancedSyntax.Upper k) (ν : Nat → Nat),
  BalancedSyntax.genuineExpression (k::Γ) E →
  BalancedSyntax.genuineExpression (k::Γ) F →
  (∀ a ∈ (BalancedSyntax.comparisonRow E F).atoms,
    threshold (BalancedSyntax.comparisonRow E F) ≤
      input (BalancedSyntax.basisValues k Γ C ν) a.2) →
  (((Collection.collect (BalancedSyntax.basisValues k Γ C ν)
      (BalancedSyntax.comparisonRow E F)).atoms = []) ∧
    (BalancedSyntax.value (k::Γ) C E ν : Int) - (BalancedSyntax.value (k::Γ) C F ν : Int) =
      (BalancedSyntax.value Γ C.1 (BalancedSyntax.Affine.lowerPart k Γ C E) ν : Int) -
        (BalancedSyntax.value Γ C.1 (BalancedSyntax.Affine.lowerPart k Γ C F) ν : Int)) ∨
    ((∃ winner : Int × Atom, GreatestSurvivor (BalancedSyntax.basisValues k Γ C ν)
        (BalancedSyntax.comparisonRow E F) winner) ∧
      ∀ winner : Int × Atom, GreatestSurvivor (BalancedSyntax.basisValues k Γ C ν)
        (BalancedSyntax.comparisonRow E F) winner →
        winner.1 ≠ 0 ∧
          Int.sign ((BalancedSyntax.value (k::Γ) C E ν : Int) -
            (BalancedSyntax.value (k::Γ) C F ν : Int)) = Int.sign winner.1)

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.CollectedDominance.Targets
