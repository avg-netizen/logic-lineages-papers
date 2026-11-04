module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Targets
open Dioph DiophantineCompletion DiophantinePolynomialBridge

def PairDiophantine : Prop := ∀ (alpha : Type) (f g : (alpha → Nat) → Nat),
  DiophFn f → DiophFn g → DiophFn (fun v => Nat.pair (f v) (g v))

def UnpairDiophantine : Prop := ∀ (alpha : Type) (f : (alpha → Nat) → Nat),
  DiophFn f →
  DiophFn (fun v => (Nat.unpair (f v)).1) ∧
  DiophFn (fun v => (Nat.unpair (f v)).2)

def PartialPairClosure : Prop := ∀ (f g : Nat →. Nat),
  Dioph (graph f) → Dioph (graph g) → Dioph (graph (partialPair f g))

def PartialCompositionClosure : Prop := ∀ (f g : Nat →. Nat),
  Dioph (graph f) → Dioph (graph g) → Dioph (graph (partialComp f g))

def RecursionFreeGraphDiophantine : Prop := ∀ (c : Nat.Partrec.Code),
  RecursionFree c → Dioph (graph (Nat.Partrec.Code.eval c))

def RecursionFreePolynomialRepresentation : Prop := ∀ (c : Nat.Partrec.Code),
  RecursionFree c → ∃ (m : Nat) (p : PolynomialCircuit.Code),
    CodeRepresents (graph (Nat.Partrec.Code.eval c)) m p

/-! Full endpoints below remain unpaid until variable-length trace/recursion
representation is proved. They are specifications, never assumed fields or
premises of the accepted recursion-free supplier clauses. -/
def UniversalEvaluatorDiophantine : Prop :=
  Dioph {v : Fin 3 → Nat |
    v 2 ∈ Nat.Partrec.Code.eval (Nat.Partrec.Code.ofNatCode (v 0)) (v 1)}

def REPolynomialReduction : Prop := ∀ (P : Nat → Prop), REPred P →
  ∃ reduce : Nat → Nat, Computable reduce ∧
    ∀ x, P x ↔ encodedPolynomialSolvable (reduce x)

def EncodedPolynomialUndecidable : Prop := ¬ ComputablePred encodedPolynomialSolvable

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Targets
