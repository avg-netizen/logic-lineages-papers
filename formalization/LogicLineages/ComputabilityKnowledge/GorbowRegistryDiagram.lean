module

public import LogicLineages.ComputabilityKnowledge.GorbowNumeralPrefixCode
public import LogicLineages.ComputabilityKnowledge.GorbowAtomicRegistry
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryChecker

@[expose] public section
/-! A concrete PA(L) registry-ground-diagram candidate, not an adequate source
Base. The unary U/u diagram is literal and decidable; uniform graph axioms,
represented provability, Hilbert--Bernays and diagonal presentation are absent. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowRegistryDiagram
open GorbowSyntax

def relationSentence (n : Nat) : Sentence := .universalRelation (Term.numeral n)
def functionSentence (n m : Nat) : Sentence :=
  .equal (.universalFunction (Term.numeral n)) (Term.numeral m)

inductive DiagramAxiom : Sentence → Prop
  | positive (n : Nat) : GorbowSortedRegistry.relationProgram n=true → DiagramAxiom (relationSentence n)
  | negative (n : Nat) : GorbowSortedRegistry.relationProgram n=false → DiagramAxiom (.neg (relationSentence n))
  | functionValue (n : Nat) : DiagramAxiom (functionSentence n (GorbowAtomicRegistry.functionProgram n))

def equationArgs (raw : List Nat) : Option (Nat × Nat) := do
  let p ← GorbowNumeralPrefixCode.parse raw
  let m ← GorbowNumeralPrefixCode.decode p.2
  pure (p.1,m)

def axiomProgram (raw : List Nat) : Bool :=
  if raw.take 1=[1] then
    ((GorbowNumeralPrefixCode.decode (raw.drop 1)).map GorbowSortedRegistry.relationProgram).getD false
  else if raw.take 2=[6,1] then
    ((GorbowNumeralPrefixCode.decode (raw.drop 2)).map (fun n => !(GorbowSortedRegistry.relationProgram n))).getD false
  else if raw.take 2=[0,5] then
    ((equationArgs (raw.drop 2)).map (fun p => decide (GorbowAtomicRegistry.functionProgram p.1=p.2))).getD false
  else false

def Theory : Sentence → Prop := GorbowTheoryChecker.ProgramTheory axiomProgram
end LogicLineages.ComputabilityKnowledge.GorbowRegistryDiagram
