module

public import LogicLineages.ComputabilityKnowledge.GorbowPRInternalCoherenceDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRInternalCoherence.Targets
open GorbowSyntax GorbowTheoryProof GorbowPRProgram GorbowPRRegistry
open GorbowSubstitution GorbowPRDefiningEquations

/-- Actual equality congruence in arbitrary output contexts, beyond the
already checked closed-term supplier. -/
def OpenTermCongruence : Prop := ∀ (A : Sentence → Prop) n ctx (t : Term n)
    (sigma tau : Fin n → Term ctx),
  (∀ i, Nonempty (Derivation A (.equal (sigma i) (tau i)))) →
  Nonempty (Derivation A (.equal (substitute sigma t) (substitute tau t)))

/-- Pointwise implication under an OPEN formula, paid inside the existing
calculus. No temporary open formula is installed as a closed theory axiom. -/
def ConditionalTermCongruence : Prop := ∀ (A : Sentence → Prop) n ctx (R : Formula ctx)
    (t : Term n) (sigma tau : Fin n → Term ctx),
  (∀ i, Nonempty (Derivation A (.imp R (.equal (sigma i) (tau i))))) →
  Nonempty (Derivation A (.imp R (.equal (substitute sigma t) (substitute tau t))))

def RegistryCoherence : Prop := ∀ n (p : Program n) tagLeft tagRight m (q : Program m),
  (nodes p)[tagLeft]? = some ⟨m,q⟩ →
  (nodes p)[tagRight]? = some ⟨m,q⟩ →
  ∀ ctx (args : List.Vector (Term ctx) m),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (call tagLeft args) (call tagRight args)))

/-- The same internal symbolic theorem in the actual named arithmetic base,
with the real padded root and alias theory; no model-to-proof inference. -/
def NamedRegistryCoherence : Prop := ∀ (pF pR : Program 1) tagLeft tagRight m (q : Program m),
  (nodes (GorbowSourceRegistryPadding.root pF pR))[tagLeft]? = some ⟨m,q⟩ →
  (nodes (GorbowSourceRegistryPadding.root pF pR))[tagRight]? = some ⟨m,q⟩ →
  ∀ ctx (args : List.Vector (Term ctx) m),
  Nonempty (Derivation (GorbowNamedDefiningTheory.Theory pF pR)
    (.equal (call tagLeft args) (call tagRight args)))

/-- A specified literal two-copy construction witnesses actual applicability
for every PR program, including arbitrary nested recursion and arity zero. -/
def ConcreteDuplicate : Prop := ∀ n (q : Program n),
  (nodes (duplicateRoot q))[leftTag]? = some ⟨n,q⟩ ∧
  (nodes (duplicateRoot q))[rightTag q]? = some ⟨n,q⟩ ∧
  ∀ ctx (args : List.Vector (Term ctx) n),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory (duplicateRoot q))
    (.equal (call leftTag args) (call (rightTag q) args)))

def Target : Prop := OpenTermCongruence ∧ ConditionalTermCongruence ∧ RegistryCoherence ∧
  NamedRegistryCoherence ∧ ConcreteDuplicate

end LogicLineages.ComputabilityKnowledge.GorbowPRInternalCoherence.Targets
