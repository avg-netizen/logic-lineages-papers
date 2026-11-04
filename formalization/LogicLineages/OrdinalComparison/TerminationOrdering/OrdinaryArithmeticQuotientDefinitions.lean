module

public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticProgramDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientCertificatesPrimrecTargets

@[expose] public section

namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticQuotient

open Source OrdinaryArithmetic
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Both endpoints use this ONE symbol window, type window and precedence
table. Only the already-supported ambient Gamma and ranked signature are
fixed parameters of the family. -/
abbrev Context (n : Nat) := (List (Fin n) × List Ty) × (Fin n → Fin n → Bool)

def contextCode {n : Nat} (symbols : List (Fin n)) (S : List Ty)
    (table : Fin n → Fin n → Bool) : Nat := Encodable.encode ((symbols, S), table)

def edgeValue (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (v : List.Vector Nat 4) : Nat :=
  ((Encodable.decode (α := Context n) (v.get 0)).any (fun ctx =>
    NumberedNumericQuotientEdge.numericEdgeTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
      (v.get 1) (v.get 2) (v.get 3))).toNat

def positiveValue (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (v : List.Vector Nat 4) : Nat :=
  ((Encodable.decode (α := Context n) (v.get 0)).any (fun ctx =>
    NumberedQuotientPathCertificates.positivePathTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
      (v.get 1) (v.get 2) (v.get 3))).toNat

/-- The certificate is the only new existential. Its input program consumes
the actual encoded context and both unchanged endpoint numbers. -/
def certificateGraph (p : Program 4) : Formula (Fin 3) :=
  existsFin (applyGraph (graphFormula p) (succTerm zeroTerm)
    ![.var (.inl 0), .var (.inl 1), .var (.inl 2), .var (.inr (0 : Fin 1))])

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticQuotient
