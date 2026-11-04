module
public import LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticQuotientProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticDirect
open Source OrdinaryArithmeticQuotient

def directValue (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (v : List.Vector Nat 4) : Nat :=
  ((Encodable.decode (α := Context n) (v.get 0)).any (fun ctx =>
    QuotientDirectCertificates.numericTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
      (v.get 1) (v.get 2) (v.get 3))).toNat

/-- Context and list validity are explicit, not assumptions about arbitrary codes. -/
def encodedDirect (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context source target : Nat) : Prop :=
  ∃ (ctx : Context n) (ss ts : List Nat),
    Encodable.decode context = some ctx ∧ Encodable.decode source = some ss ∧
    Encodable.decode target = some ts ∧
    DirectMultisetPresentation.Direct
      (QuotientDominationCertificates.relation n arity ctx.1.1 ctx.1.2 Gamma ctx.2) ss ts

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticDirect
