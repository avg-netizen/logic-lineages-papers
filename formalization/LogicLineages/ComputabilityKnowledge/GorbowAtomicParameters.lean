module

public import LogicLineages.ComputabilityKnowledge.GorbowAtomicRegistry
public import LogicLineages.ComputabilityKnowledge.GorbowNameDictionary

@[expose] public section
/-! Literal nested restricted source binders and arbitrary-name parameter
code/value dictionaries. Unused code slots contain the tagged code of zero,
not numeric zero; unused value slots contain the zero term. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowAtomicParameters
open GorbowSyntax GorbowRegistryTuple GorbowSortedSyntaxCode GorbowSortedQuantifierTruth

def arithmeticClosure : {n : Nat} → Formula n → Sentence
  | 0,φ => φ
  | n+1,φ => arithmeticClosure (n:=n) (.all (.imp (arithmeticTermGuard (.var 0)) φ))

def evaluationTerm {n : Nat} (t : Term n) : Term n :=
  .universalFunction (headerTerm 1 1 [t])

def codeDictionary {n m : Nat} (names : Fin n → Fin m) : Fin m → Term n :=
  fun i => (List.ofFn (fun j : Fin n => Term.var j)).getD
    ((GorbowNameDictionary.namesList names).idxOf i.val)
    (Term.numeral (termCode (.zero : Term 0)))

def valueDictionary {n m : Nat} (names : Fin n → Fin m) : Fin m → Term n :=
  GorbowNameDictionary.dictionary names (fun j => evaluationTerm (.var j))

def argumentTuple {n m : Nat} (names : Fin n → Fin m) : Term n :=
  tupleTerm (List.ofFn (codeDictionary names))
end LogicLineages.ComputabilityKnowledge.GorbowAtomicParameters
