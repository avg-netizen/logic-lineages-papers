module

public import LogicLineages.ComputabilityKnowledge.GorbowOrdinaryArithmeticGraphsDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowOrdinaryArithmeticGraphs.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof
open LogicLineages.OrdinalComparison.TerminationOrdering

def TermImage : Prop := ∀ (alpha : Type) (m : Nat) (rho : alpha → Fin m) (t : OrdinaryArithmetic.Term alpha),
  GorbowStandardInstances.ArithmeticTerm (translateTerm rho t)

def FormulaImage : Prop := ∀ (alpha : Type) (l m : Nat)
    (a : OrdinaryArithmetic.arithmeticLanguage.BoundedFormula alpha l) (free : alpha → Fin m) (bound : Fin l → Fin m),
  ArithmeticFormula (translateBounded a free bound)

def TermTruth : Prop := ∀ (alpha : Type) (m : Nat) (I : Interpretation)
    (rho : alpha → Fin m) (t : OrdinaryArithmetic.Term alpha) (v : Fin m → Nat),
  (translateTerm rho t).realize I v = t.realize (fun i => v (rho i))

def BoundedTruth : Prop := ∀ (alpha : Type) (l m : Nat) (I : Interpretation)
    (a : OrdinaryArithmetic.arithmeticLanguage.BoundedFormula alpha l) (free : alpha → Fin m)
    (bound : Fin l → Fin m) (v : Fin m → Nat),
  (translateBounded a free bound).realize I v ↔
    a.Realize (fun i => v (free i)) (fun i => v (bound i))

/-- The ACTUAL structural graph, with no U/u/K/T or proof-checker atom. -/
def ProgramTruth : Prop := ∀ (n : Nat) (p : Program n) (I : Interpretation) (v : Fin (n+1) → Nat),
  (graph p).realize I v ↔ evaluate p (List.Vector.ofFn (fun i => v i.succ)) = v 0

/-- Complete standard arithmetic representation, not yet internal totality or
uniqueness for general PR recursion. -/
def AllPrimitiveGraphs : Prop := ∀ (n : Nat) (f : List.Vector Nat n → Nat), Primrec f →
  ∃ a : Formula (n+1), ArithmeticFormula a ∧ ∀ (I : Interpretation) (v : Fin (n+1) → Nat),
    a.realize I v ↔ f (List.Vector.ofFn (fun i => v i.succ)) = v 0

/-- UNCONDITIONAL actual Hilbert numeral proofs at the three initial program
constructors, using only the paid PA(L) logic. No graph-correctness axiom. -/
def InitialCertificates : Prop :=
  (∀ (T : Sentence → Prop),
    Nonempty (Derivation T (closedGraph .zero List.Vector.nil 0))) ∧
  (∀ (T : Sentence → Prop) (inputs : List.Vector Nat 1),
    Nonempty (Derivation T (closedGraph .succ inputs (inputs.get 0 + 1)))) ∧
  (∀ (T : Sentence → Prop) (n : Nat) (i : Fin n) (inputs : List.Vector Nat n),
    Nonempty (Derivation T (closedGraph (.projection i) inputs (inputs.get i))))

def Target : Prop := TermImage ∧ FormulaImage ∧ TermTruth ∧ BoundedTruth ∧
  ProgramTruth ∧ AllPrimitiveGraphs ∧ InitialCertificates
end LogicLineages.ComputabilityKnowledge.GorbowOrdinaryArithmeticGraphs.Targets
