module

public import LogicLineages.ComputabilityKnowledge.GorbowProgramDiagram
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowProgramDiagram
open GorbowSyntax GorbowTheoryProof GorbowSortedRevision
open GorbowRegistryDiagram (relationSentence functionSentence)
open LogicLineages.ComputabilityKnowledge.GorbowProgramDiagram

def ExactProgram : Prop := ∀ R F raw,
  axiomProgram R F raw=true ↔ ∃ σ : Sentence, raw=GorbowFormulaPrefixCode.encode σ ∧ DiagramAxiom R F σ

def ActualTheory : Prop := ∀ R F (σ : Sentence), Theory R F σ ↔ DiagramAxiom R F σ

def DiagramSoundness : Prop := ∀ R F (P : Extension) (σ : Sentence), DiagramAxiom R F σ →
  σ.realize (interpretation (ground R F) P) Fin.elim0

def TheorySoundness : Prop := ∀ R F (P : Extension) n (φ : Formula n), Derivation (Theory R F) φ →
  ∀ v, φ.realize (interpretation (ground R F) P) v

def NumeralwiseRepresentation : Prop := ∀ R F,
  (∀ n, Nonempty (Derivation (Theory R F) (relationSentence n)) ↔ R n=true) ∧
  (∀ n, Nonempty (Derivation (Theory R F) (.neg (relationSentence n))) ↔ R n=false) ∧
  (∀ n m, Nonempty (Derivation (Theory R F) (functionSentence n m)) ↔ F n=m)

def DiagramConsistency : Prop := ∀ R F, ¬ Nonempty (Derivation (Theory R F) falseEquality)

def UniformProgram : Prop := ∀ R F, Primrec R → Primrec F → Primrec (axiomProgram R F)

def Target : Prop := ExactProgram ∧ ActualTheory ∧ DiagramSoundness ∧ TheorySoundness ∧
  NumeralwiseRepresentation ∧ DiagramConsistency ∧ UniformProgram
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowProgramDiagram
