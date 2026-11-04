module
public import LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectPrimrecDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectPrimrecTargets
open QuotientDirectPrimrec

def ActualDominationPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Source.Ty), Primrec (fun p : Parameters n × List Nat × List Nat × List QuotientDominationCertificates.Entry => QuotientDominationCertificates.test n arity p.1.1.1 p.1.1.2 Gamma p.1.2 p.2.1 p.2.2.1 p.2.2.2)

def ActualDirectPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Source.Ty), Primrec (fun p : Parameters n × List Nat × List Nat × QuotientDirectCertificates.Certificate => QuotientDirectCertificates.directTest n arity p.1.1.1 p.1.1.2 Gamma p.1.2 p.2.1 p.2.2.1 p.2.2.2)

def ActualNumericDirectPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Source.Ty), Primrec (fun p : Parameters n × Nat × Nat × Nat => QuotientDirectCertificates.numericTest n arity p.1.1.1 p.1.1.2 Gamma p.1.2 p.2.1 p.2.2.1 p.2.2.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectPrimrecTargets
