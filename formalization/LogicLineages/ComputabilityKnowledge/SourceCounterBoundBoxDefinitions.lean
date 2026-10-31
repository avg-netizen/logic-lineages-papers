module
public import LogicLineages.ComputabilityKnowledge.SourceCounterBoundSearchProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.SourceCounterBoundBox
/-- Zero-based entries represent positive coordinates `x+1`. -/
def box (r : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | m+1 => (List.range r).flatMap fun x => (box r m).map (x :: ·)
/-- Test exactly the first `n` entries; final callers use the list's length. -/
def failingPrefix {Q : Type*} (point : Q → List Nat → Bool) (q : Q)
    (tuples : List (List Nat)) : Nat → Bool
  | 0 => false
  | n+1 => failingPrefix point q tuples n || !(point q (tuples.getD n []))
def radiusBad {Q : Type*} (arity : Q → Nat) (point : Q → List Nat → Bool)
    (q : Q) (r : Nat) : Bool :=
  failingPrefix point q (box r (arity q)) (box r (arity q)).length
end LogicLineages.ComputabilityKnowledge.SourceCounterBoundBox
