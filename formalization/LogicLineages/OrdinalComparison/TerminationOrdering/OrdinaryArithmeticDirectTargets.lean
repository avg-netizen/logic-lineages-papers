module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticDirectDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticDirectTargets
open OrdinaryArithmeticDirect

def EncodedCheckerPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Source.Ty), Primrec (directValue n arity Gamma)

def ActualCheckerCalibration : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Source.Ty) (symbols : List (Fin n)) (S : List Source.Ty) (table : Fin n → Fin n → Bool) (x y c : Nat), directValue n arity Gamma (List.Vector.ofFn ![OrdinaryArithmeticQuotient.contextCode symbols S table,x,y,c]) = (QuotientDirectCertificates.numericTest n arity symbols S Gamma table x y c).toNat

def EncodedDirectFormula : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Source.Ty), ∃ p : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 4, (∀ v, LogicLineages.ComputabilityKnowledge.GorbowPRProgram.evaluate p v = directValue n arity Gamma v) ∧ ∀ ctx x y : Nat, (OrdinaryArithmeticQuotient.certificateGraph p).Realize ![ctx,x,y] ↔ encodedDirect n arity Gamma ctx x y

def UniformDirectFormula : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Source.Ty), ∃ phi : OrdinaryArithmetic.Formula (Fin 3), ∀ (symbols : List (Fin n)) (S : List Source.Ty) (table : Fin n → Fin n → Bool) (source target : List Nat), phi.Realize ![OrdinaryArithmeticQuotient.contextCode symbols S table,Encodable.encode source,Encodable.encode target] ↔ DirectMultisetPresentation.Direct (QuotientDominationCertificates.relation n arity symbols S Gamma table) source target

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticDirectTargets
