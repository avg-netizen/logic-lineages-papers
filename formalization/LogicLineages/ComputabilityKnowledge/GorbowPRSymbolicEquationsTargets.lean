module

public import LogicLineages.ComputabilityKnowledge.GorbowPRSymbolicEquationsDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRSymbolicEquations.Targets
open GorbowSyntax GorbowTheoryProof GorbowPRProgram GorbowPRRegistry
open GorbowPRDefiningEquations GorbowPRNumeralCalculation GorbowPRChildTags
open GorbowSubstitution List.Vector

/-- Genuine Hilbert specialization of an actual universally closed axiom,
with arbitrary free terms in the output context. -/
def OpenAxiomSpecialization : Prop := ∀ (A : Sentence → Prop) n ctx (phi : Formula n)
    (sigma : Fin n → Term ctx), A (GorbowStandardInduction.universalClosure phi) →
  Nonempty (Derivation A (symbolicInstance phi sigma))

/-- Actual finite-registry membership, with literal node equations; neither
semantic validity nor an assumed representability premise occurs. -/
def NodeEquationInstances : Prop := ∀ n (p : Program n) tag m (q : Program m),
  (nodes p)[tag]?=some ⟨m,q⟩ → ∀ arity ctx (lhs rhs : Term arity),
  equation lhs rhs ∈ nodeEquations q tag → ∀ sigma : Fin arity → Term ctx,
  Nonempty (Derivation (Theory p)
    (.equal (substitute sigma lhs) (substitute sigma rhs)))

def CompositionEquation : Prop := ∀ n (p : Program n) tag m k
    (f : Program k) (g : Fin k → Program m),
  (nodes p)[tag]?=some ⟨m,.composition f g⟩ → ∀ ctx (args : List.Vector (Term ctx) m),
  Nonempty (Derivation (Theory p) (.equal (call tag args)
    (call (tag+1) (List.Vector.ofFn fun i => call (tag+argumentTag f g i) args))))

def RecursionZeroEquation : Prop := ∀ n (p : Program n) tag m
    (f : Program m) (g : Program (m+2)),
  (nodes p)[tag]?=some ⟨m+1,.recursion f g⟩ → ∀ ctx (args : List.Vector (Term ctx) m),
  Nonempty (Derivation (Theory p)
    (.equal (call tag (.zero ::ᵥ args)) (call (tag+1) args)))

def RecursionSuccessorEquation : Prop := ∀ n (p : Program n) tag m
    (f : Program m) (g : Program (m+2)),
  (nodes p)[tag]?=some ⟨m+1,.recursion f g⟩ → ∀ ctx (x : Term ctx)
    (args : List.Vector (Term ctx) m),
  Nonempty (Derivation (Theory p) (.equal (call tag (.succ x ::ᵥ args))
    (call (tag+stepTag f) (x ::ᵥ call tag (x ::ᵥ args) ::ᵥ args))))

def Target : Prop := OpenAxiomSpecialization ∧ NodeEquationInstances ∧ CompositionEquation ∧
  RecursionZeroEquation ∧ RecursionSuccessorEquation

end LogicLineages.ComputabilityKnowledge.GorbowPRSymbolicEquations.Targets
