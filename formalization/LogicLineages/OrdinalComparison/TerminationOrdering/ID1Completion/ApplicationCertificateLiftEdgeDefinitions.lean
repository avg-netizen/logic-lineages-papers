module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericQuotientEdgeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftEdge
open NumberedNumericQuotientEdge ApplicationCertificateLift

def sourceOf (certificate : Nat) : Nat := (Nat.unpair certificate).1
def targetOf (certificate : Nat) : Nat := (Nat.unpair (Nat.unpair certificate).2).1
def stepOf (certificate : Nat) : Nat := (Nat.unpair (Nat.unpair certificate).2).2

/-- Lift the literal original source/target/step fields. Neither the original
step certificate nor its replacement/root data is replaced by a new witness. -/
def liftEdge (domain codomain argument certificate : Nat) : Nat :=
  edgeCertificateNumber
    (rawApplication domain codomain (sourceOf certificate) argument)
    (rawApplication domain codomain (targetOf certificate) argument)
    (liftStep (stepOf certificate))

def edgeValue (v : List.Vector Nat 4) : Nat :=
  liftEdge (v.get 0) (v.get 1) (v.get 2) (v.get 3)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftEdge
