module

public import LogicLineages.ComputabilityKnowledge.GorbowArithmeticCompositionCertificatesDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowArithmeticCompositionCertificates.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof
open LogicLineages.OrdinalComparison.TerminationOrdering

/-- Actual closed Hilbert introduction for the EXACT encoded existential. -/
def WitnessIntroduction : Prop := ∀ (T : Sentence → Prop) (a : Formula 1) (t : Term 0),
  Nonempty (Derivation T (GorbowStandardInstances.instantiate a t)) →
    Nonempty (Derivation T (encodedExists a))

/-- Literal finite conjunctions emitted by the paid ordinary compiler. -/
def FiniteConjunction : Prop := ∀ (T : Sentence → Prop) (k n : Nat)
    (a : Fin k → OrdinaryArithmetic.Formula (Fin n)) (v : Fin n → Nat),
  (∀ i, Nonempty (Derivation T (closedArithmetic (a i) v))) →
    Nonempty (Derivation T (closedArithmetic (OrdinaryArithmetic.andFin a) v))

/-- Subproofs are actual Hilbert derivations of the ACTUAL subprogram graphs;
the final all-fragment target below discharges them by structural induction. -/
def CompositionCertificates : Prop := ∀ (T : Sentence → Prop) (m k : Nat)
    (f : Program k) (g : Fin k → Program m) (inputs : List.Vector Nat m)
    (middle : List.Vector Nat k) (out : Nat),
  Nonempty (Derivation T (GorbowOrdinaryArithmeticGraphs.closedGraph f middle out)) →
  (∀ i, Nonempty (Derivation T
    (GorbowOrdinaryArithmeticGraphs.closedGraph (g i) inputs (middle.get i)))) →
  Nonempty (Derivation T
    (GorbowOrdinaryArithmeticGraphs.closedGraph (.composition f g) inputs out))

/-- Unconditional internal arithmetic numeral representation for the ENTIRE
actual recursion-free fragment; no correctness premise survives. -/
def RecursionFreeCertificates : Prop := ∀ (T : Sentence → Prop) (n : Nat)
    (p : Program n), recursionFree p → ∀ inputs : List.Vector Nat n,
  Nonempty (Derivation T
    (GorbowOrdinaryArithmeticGraphs.closedGraph p inputs (evaluate p inputs)))

def Target : Prop := WitnessIntroduction ∧ FiniteConjunction ∧
  CompositionCertificates ∧ RecursionFreeCertificates
end LogicLineages.ComputabilityKnowledge.GorbowArithmeticCompositionCertificates.Targets
