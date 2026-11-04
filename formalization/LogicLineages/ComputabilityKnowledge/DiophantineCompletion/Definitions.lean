module
public import LogicLineages.ComputabilityKnowledge.DiophantinePolynomialBridgeProof
public import Mathlib.Computability.Halting

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion

/-- The actual ordinary partial-function graph: coordinate zero is input and
coordinate one is output. Undefined computations have no graph point. -/
def graph (f : Nat →. Nat) : Set (Fin 2 → Nat) :=
  {v | v 1 ∈ f (v 0)}

def partialPair (f g : Nat →. Nat) : Nat →. Nat :=
  fun x => (f x).bind (fun a => (g x).map (Nat.pair a))

def partialComp (f g : Nat →. Nat) : Nat →. Nat :=
  fun x => (g x).bind f

/-- A syntactic fragment of the UNCHANGED ordinary Mathlib code datatype.
The missing primitive-recursion and minimization constructors are not silently
included or represented by a supplier premise. -/
inductive RecursionFree : Nat.Partrec.Code → Prop where
  | zero : RecursionFree .zero
  | succ : RecursionFree .succ
  | left : RecursionFree .left
  | right : RecursionFree .right
  | pair {f g} : RecursionFree f → RecursionFree g → RecursionFree (.pair f g)
  | comp {f g} : RecursionFree f → RecursionFree g → RecursionFree (.comp f g)

/-- Shared S1/S5 Hilbert-tenth convention. Existing actual polynomial code,
integer coefficients, zero-allowing finite natural witnesses, and genuine
MvPolynomial evaluation are retained; malformed or ill-formed codes fail. -/
def encodedPolynomialSolvable (e : Nat) : Prop :=
  ∃ (xs : List Nat) (p : PolynomialCircuit.Code),
    Encodable.decode e = some xs ∧ PolynomialCircuit.decode xs = some p ∧
    p.WellFormed ∧ PolynomialDomainShift.HasNonnegativeRoot p

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion
