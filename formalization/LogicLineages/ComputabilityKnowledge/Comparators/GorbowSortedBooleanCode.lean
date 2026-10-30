module

public import LogicLineages.ComputabilityKnowledge.GorbowSortedBooleanCode
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedBooleanCode
open GorbowSyntax GorbowSortedSyntaxCode GorbowStandardInstances
open LogicLineages.ComputabilityKnowledge.GorbowSortedBooleanCode

def RawConstructors : Prop :=
  (∀ tag raw, unaryNumber tag (formulaRawNumber raw)=formulaRawNumber (GorbowCodeConstructors.unary tag raw)) ∧
  (∀ tag a b, binaryNumber tag (formulaRawNumber a) (formulaRawNumber b)=formulaRawNumber (GorbowCodeConstructors.binary tag a b))

def ActualConstructors : Prop := ∀ n (φ ψ : Formula n),
  unaryNumber 6 (formulaCode φ)=formulaCode (.neg φ) ∧
  binaryNumber 7 (formulaCode φ) (formulaCode ψ)=formulaCode (.imp φ ψ) ∧
  binaryNumber 8 (formulaCode φ) (formulaCode ψ)=formulaCode (.conj φ ψ) ∧
  binaryNumber 9 (formulaCode φ) (formulaCode ψ)=formulaCode (.disj φ ψ)

def ExactDomains : Prop :=
  (∀ code, sentenceCode code=true ↔ ∃ σ : Sentence, code=formulaCode σ) ∧
  (∀ code, fullTermCode code=true ↔ ∃ t : Term 0, code=termCode t) ∧
  (∀ code, arithmeticTermCode code=true ↔ ∃ t : Term 0, code=termCode t ∧ ArithmeticTerm t)

def WrongSortRejection : Prop :=
  (∀ n (t : Term n) tag, unaryNumber tag (termCode t)=0 ∧ sentenceCode (termCode t)=false) ∧
  (∀ n (t : Term n) tag other, binaryNumber tag (termCode t) other=0 ∧ binaryNumber tag other (termCode t)=0) ∧
  (∀ n (φ : Formula n), fullTermCode (formulaCode φ)=false ∧ arithmeticTermCode (formulaCode φ)=false)

def UniformPrograms : Prop :=
  Primrec (fun p : Nat × Nat => unaryNumber p.1 p.2) ∧
  Primrec (fun p : Nat × Nat × Nat => binaryNumber p.1 p.2.1 p.2.2) ∧
  Primrec sentenceCode ∧ Primrec fullTermCode ∧ Primrec arithmeticTermCode

def Target : Prop := RawConstructors ∧ ActualConstructors ∧ ExactDomains ∧ WrongSortRejection ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedBooleanCode
