module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchProvenanceDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchProvenanceTargets
open NormalForm PlainBranchProvenance

def ExactLinearityDetection : Prop := ∀ (i : Nat) (p : Formula),
  LinearRows.isLinear i p = true ↔ ∀ s ∈ nonlinearOccurrences p, s.name ≠ i

def ExactPlainDetection : Prop := ∀ p : Formula,
  MaximalPlainBranch.isPlain p = true ↔ ∀ s ∈ LinearBlock.occurrences p, plain s = true

def LinearGuards : Prop := ∀ (inputs : List ShiftedInputGuards.Input)
    (g : CommonHeadLargeGuards.Formula),
  nonlinearOccurrences (ShiftedInputGuards.compile inputs g) = []

def LiteralAtomicProvenance : Prop := ∀ (i : Nat) (a : Atom) (s : Summand),
  s ∈ nonlinearOccurrences (MaximalPlainRows.compileAtom i a) →
    s ∈ nonlinearOccurrences (.atom a)

/-- The actual elimination removes the chosen name and never invents a nonlinear
summand. No plain-syntax or semantic precondition is needed for this syntax fact. -/
def LiteralBranchProvenance : Prop := ∀ (i : Nat) (p : Formula) (s : Summand),
  s ∈ nonlinearOccurrences (MaximalPlainBranch.eliminate i p) →
    s.name ≠ i ∧ s ∈ nonlinearOccurrences p

def PreservePlain : Prop := ∀ (i : Nat) (p : Formula), MaximalPlainBranch.isPlain p = true →
  MaximalPlainBranch.isPlain (MaximalPlainBranch.eliminate i p) = true

def StrictNameDecrease : Prop := ∀ (i : Nat) (p : Formula), i ∈ nonlinearNames p →
  (nonlinearNames (MaximalPlainBranch.eliminate i p)).card < (nonlinearNames p).card

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchProvenanceTargets
