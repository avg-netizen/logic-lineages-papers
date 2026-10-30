module

public import LogicLineages.ComputabilityKnowledge.GorbowSortedSimultaneousCode

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedSimultaneousCode
open GorbowSyntax GorbowSortedSyntaxCode GorbowFormulaSubstitution
open LogicLineages.ComputabilityKnowledge.GorbowSortedSimultaneousCode

def DictionaryCalibration : Prop := ∀ n (σ : Fin n → Term 0),
  dictionaryOK n (List.ofFn (fun i => termCode (σ i)))=true ∧
  dictionaryRaw (List.ofFn (fun i => termCode (σ i)))=GorbowLiftedDictionary.dictionary σ

def ExactDictionary : Prop := ∀ n codes, dictionaryOK n codes=true ↔
  ∃ σ : Fin n → Term 0, codes=List.ofFn (fun i => termCode (σ i))

def ExactOutput : Prop := ∀ n code codes out,
  substituteNumber n code codes=some out ↔ ∃ (φ : Formula n) (σ : Fin n → Term 0),
    code=formulaCode φ ∧ codes=List.ofFn (fun i => termCode (σ i)) ∧
    out=formulaCode (substituteFormula σ φ)

def ActualCalibration : Prop := ∀ n (φ : Formula n) (σ : Fin n → Term 0),
  substituteNumber n (formulaCode φ) (List.ofFn (fun i => termCode (σ i)))=
    some (formulaCode (substituteFormula σ φ))

def ExactRejection : Prop := ∀ n code codes,
  substituteNumber n code codes=none ↔
    dictionaryOK n codes=false ∨ ¬ ∃ φ : Formula n, code=formulaCode φ

def UniformPrograms : Prop := Primrec dictionaryRaw ∧
  Primrec (fun p : Nat × List Nat => dictionaryOK p.1 p.2) ∧
  Primrec (fun p : Nat × Nat × List Nat => substituteNumber p.1 p.2.1 p.2.2)

def Target : Prop := DictionaryCalibration ∧ ExactDictionary ∧ ExactOutput ∧
  ActualCalibration ∧ ExactRejection ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedSimultaneousCode
