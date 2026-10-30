module

public import LogicLineages.ComputabilityKnowledge.GorbowRegistryDiagram
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowRegistryDiagram
open GorbowSyntax GorbowTheoryProof GorbowSortedRevision
open LogicLineages.ComputabilityKnowledge.GorbowRegistryDiagram

def EquationArgsExact : Prop := ∀ raw n m,
  equationArgs raw=some (n,m) ↔ raw=GorbowCodeConstructors.numeral n ++ GorbowCodeConstructors.numeral m

def ExactProgram : Prop := ∀ raw,
  axiomProgram raw=true ↔ ∃ σ : Sentence, raw=GorbowFormulaPrefixCode.encode σ ∧ DiagramAxiom σ

def ActualTheory : Prop := ∀ σ : Sentence, Theory σ ↔ DiagramAxiom σ

def DiagramSoundness : Prop := ∀ (P : Extension) (σ : Sentence), DiagramAxiom σ →
  σ.realize (interpretation GorbowAtomicRegistry.ground P) Fin.elim0

def TheorySoundness : Prop := ∀ (P : Extension) n (φ : Formula n), Derivation Theory φ →
  ∀ v, φ.realize (interpretation GorbowAtomicRegistry.ground P) v

def NumeralwiseRepresentation : Prop :=
  (∀ n, Nonempty (Derivation Theory (relationSentence n)) ↔ GorbowSortedRegistry.relationProgram n=true) ∧
  (∀ n, Nonempty (Derivation Theory (.neg (relationSentence n))) ↔ GorbowSortedRegistry.relationProgram n=false) ∧
  (∀ n m, Nonempty (Derivation Theory (functionSentence n m)) ↔ GorbowAtomicRegistry.functionProgram n=m)

def DiagramConsistency : Prop := ¬ Nonempty (Derivation Theory falseEquality)

def UniformPrograms : Prop := Primrec equationArgs ∧ Primrec axiomProgram

def Target : Prop := EquationArgsExact ∧ ExactProgram ∧ ActualTheory ∧ DiagramSoundness ∧
  TheorySoundness ∧ NumeralwiseRepresentation ∧ DiagramConsistency ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowRegistryDiagram
