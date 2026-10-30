module

public import LogicLineages.ComputabilityKnowledge.GorbowRegistryDiagram

@[expose] public section
/-! Literal ground-diagram construction for explicit relation/function programs.
No representation-correctness field is assumed: all semantic and proof claims
are proved for the actual ground below. Recursiveness is conditional only on
primitive recursion of the two actual programs, paid separately at instances. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowProgramDiagram
open GorbowSyntax
open GorbowRegistryDiagram (relationSentence functionSentence equationArgs)

inductive DiagramAxiom (R : Nat → Bool) (F : Nat → Nat) : Sentence → Prop
  | positive (n : Nat) : R n=true → DiagramAxiom R F (relationSentence n)
  | negative (n : Nat) : R n=false → DiagramAxiom R F (.neg (relationSentence n))
  | functionValue (n : Nat) : DiagramAxiom R F (functionSentence n (F n))

def axiomProgram (R : Nat → Bool) (F : Nat → Nat) (raw : List Nat) : Bool :=
  if raw.take 1=[1] then
    ((GorbowNumeralPrefixCode.decode (raw.drop 1)).map R).getD false
  else if raw.take 2=[6,1] then
    ((GorbowNumeralPrefixCode.decode (raw.drop 2)).map (fun n => !(R n))).getD false
  else if raw.take 2=[0,5] then
    ((equationArgs (raw.drop 2)).map (fun p => decide (F p.1=p.2))).getD false
  else false

def Theory (R : Nat → Bool) (F : Nat → Nat) : Sentence → Prop :=
  GorbowTheoryChecker.ProgramTheory (axiomProgram R F)

def ground (R : Nat → Bool) (F : Nat → Nat) : GorbowSortedRevision.Ground :=
  ⟨fun n => R n=true,F⟩
end LogicLineages.ComputabilityKnowledge.GorbowProgramDiagram
