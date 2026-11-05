module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.RowPackingDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.RowPackingTargets
open Elementary Cipher RowPacking

def ConstantSpecification : Prop := ∀ len q c a (f : Nat → Nat),
  IsCipherOf len q f a → (CipherRelation.Const len q c a ↔ ∀ i, i<len → f i=c)

def PackedConstraintSpecification : Prop := ∀ n k len q I (ν : Fin n → Nat)
    (codes : Fin k → Nat) (rows : Nat → Fin k → Nat)
    (c : Constraint (Option (Fin n)) (Fin k)),
  IsCipherOf len q id I →
  (∀ b, IsCipherOf len q (fun i => rows i b) (codes b)) →
  (packedConstraint len q I ν codes c ↔ ∀ i, i<len → c.Holds (indexed i ν) (rows i))

/-- Actual variable-length witness packing. Both directions preserve the
original parameter valuation, including zero length and empty finite blocks. -/
def VariableRowPacking : Prop := ∀ n k m (C : Fin m → Constraint (Option (Fin n)) (Fin k))
    len (ν : Fin n → Nat), pointwise C len ν ↔ packed C len ν

/-- A variable number of existential elementary rows, not merely a fixed
finite conjunction. No bounded-universal closure premise is assumed. -/
def PointwiseElementaryDiophantine : Prop :=
  ∀ n k m (C : Fin m → Constraint (Option (Fin n)) (Fin k)),
    Dioph {v : Option (Fin n) → Nat | pointwise C (v none) (fun a => v (some a))}

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.RowPackingTargets
