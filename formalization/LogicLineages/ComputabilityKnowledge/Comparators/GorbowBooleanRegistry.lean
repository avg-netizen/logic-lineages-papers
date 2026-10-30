module

public import LogicLineages.ComputabilityKnowledge.GorbowBooleanRegistry
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowBooleanRegistry
open GorbowSyntax GorbowCodeConstructors GorbowRegistryTuple GorbowRegistryDecoder GorbowNumericCertificate
open LogicLineages.ComputabilityKnowledge.GorbowBooleanRegistry

def NumericConstructors : Prop :=
  (∀ tag raw, unaryNumber tag (number raw)=number (unary tag raw)) ∧
  (∀ tag a b, binaryNumber tag (number a) (number b)=number (binary tag a b))

def ExactSentencehood : Prop := ∀ code, sentenceCode code=true ↔ ∃ σ : Sentence, code=formulaNumber σ

def ExactRelation : Prop := ∀ code, relationProgram code=true ↔
  ∃ σ : Sentence, code=header 1 0 [formulaNumber σ]

def FunctionCalibration : Prop := ∀ σ τ : Sentence,
  functionProgram (header 1 0 [formulaNumber σ])=formulaNumber (.neg σ) ∧
  functionProgram (header 2 0 [formulaNumber σ,formulaNumber τ])=formulaNumber (.imp σ τ) ∧
  functionProgram (header 2 1 [formulaNumber σ,formulaNumber τ])=formulaNumber (.conj σ τ) ∧
  functionProgram (header 2 2 [formulaNumber σ,formulaNumber τ])=formulaNumber (.disj σ τ)

def MalformedDefaults : Prop :=
  (∀ code, decodeHeader code=none → relationProgram code=false ∧ functionProgram code=0) ∧
  (∀ arity tag args, ¬ (arity=1 ∧ tag=0 ∧ args.length=1) → relationProgram (header arity tag args)=false) ∧
  (∀ arity tag args, ¬ (arity=1 ∧ tag=0 ∧ args.length=1) →
    ¬ (arity=2 ∧ tag<3 ∧ args.length=2) → functionProgram (header arity tag args)=0) ∧
  (∀ tag code, decodeFormula code=none → unaryNumber tag code=0) ∧
  (∀ tag a b, decodeFormula a=none ∨ decodeFormula b=none → binaryNumber tag a b=0)

def UniformPrograms : Prop :=
  Primrec (fun p : Nat × Nat => unaryNumber p.1 p.2) ∧
  Primrec (fun p : Nat × Nat × Nat => binaryNumber p.1 p.2.1 p.2.2) ∧
  Primrec sentenceCode ∧ Primrec relationProgram ∧ Primrec functionProgram

def Target : Prop := NumericConstructors ∧ ExactSentencehood ∧ ExactRelation ∧ FunctionCalibration ∧ MalformedDefaults ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowBooleanRegistry
