module

public import LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BoundedRangeDefinitions
public import LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.SelectedVerifierTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BoundedRange.Targets
open GorbowSyntax GorbowTheoryProof

def CompilerGuard : Prop :=
  ∀ m bound, guard (m := m) bound = literalGuard bound

def GuardSemantics : Prop :=
  ∀ m bound (I : Interpretation) (env : Fin (m+1) → Nat),
    (guard bound).realize I env ↔ env 0 < bound

/-- Actual PA finite-range elimination, uniformly in ALL retained parameters.
No validity-to-proof inference or finite-domain assumption is supplied. -/
def RangeElimination : Prop :=
  ∀ (T : Sentence → Prop) m bound,
    Nonempty (Derivation T (.all (.imp (guard (m := m) bound) (casesBelow bound))))

/-- Closed finite range bound, arbitrary open full-L matrix, actual proofs of
every numeral instance. The conclusion retains the original parameters. -/
def BoundedGeneralization : Prop :=
  ∀ (T : Sentence → Prop) m bound (phi : Formula (m+1)),
    (∀ i : Fin bound, Nonempty (Derivation T
      (GorbowStandardInstances.instantiate phi (Term.numeral i.val)))) →
    Nonempty (Derivation T (bounded bound phi))

def Target : Prop := CompilerGuard ∧ GuardSemantics ∧ RangeElimination ∧ BoundedGeneralization

end LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BoundedRange.Targets
