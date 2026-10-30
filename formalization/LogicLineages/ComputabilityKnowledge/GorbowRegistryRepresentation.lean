module

public import LogicLineages.ComputabilityKnowledge.GorbowRegistryDiagram
public import LogicLineages.ComputabilityKnowledge.GorbowArithmeticDerivation
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryNumericCertificate

@[expose] public section
/-! Numeralwise actual registry representation at closed arithmetic inputs,
including literal polynomial header expressions. The checker is an external
certificate checker, not an internally represented proof predicate. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowRegistryRepresentation
open GorbowSyntax

def inputValue (s : Term 0) : Nat :=
  s.realize (GorbowSortedRevision.interpretation GorbowAtomicRegistry.ground (fun _ => False)) Fin.elim0

def headerInput (arity tag : Nat) (args : List Nat) : Term 0 :=
  GorbowRegistryTuple.headerTerm arity tag (args.map Term.numeral)

def check (n formula certificate : Nat) : Bool :=
  GorbowTheoryNumericCertificate.check GorbowRegistryDiagram.axiomProgram n formula certificate
end LogicLineages.ComputabilityKnowledge.GorbowRegistryRepresentation
