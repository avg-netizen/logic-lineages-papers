module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundWeakeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRenamingCompositionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundContextTower
open Source

def groundContext : Nat → List Ty → List Ty
  | 0, Gamma => Gamma
  | k + 1, Gamma => .ground :: groundContext k Gamma

def groundRenaming (k : Nat) (Gamma : List Ty) : Renaming Gamma (groundContext k Gamma) :=
  match k with
  | 0 => fun v => v
  | k + 1 => fun v => .there (groundRenaming k Gamma v)
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundContextTower
