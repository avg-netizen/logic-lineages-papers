module

public import LogicLineages.ComputabilityKnowledge.GorbowCodeConstructors

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowCodeConstructors
open GorbowSyntax
open LogicLineages.ComputabilityKnowledge.GorbowCodeConstructors

def TermConstructors : Prop := ∀ (n : Nat),
  (∀ i : Fin n, GorbowTermPrefixCode.encode (.var i) = variableCode i.val) ∧
  GorbowTermPrefixCode.encode (Term.zero : Term n) = [1] ∧
  (∀ t : Term n, GorbowTermPrefixCode.encode (.succ t) = unary 2 (GorbowTermPrefixCode.encode t)) ∧
  (∀ t u : Term n, GorbowTermPrefixCode.encode (.add t u) = binary 3 (GorbowTermPrefixCode.encode t) (GorbowTermPrefixCode.encode u)) ∧
  (∀ t u : Term n, GorbowTermPrefixCode.encode (.mul t u) = binary 4 (GorbowTermPrefixCode.encode t) (GorbowTermPrefixCode.encode u)) ∧
  (∀ t : Term n, GorbowTermPrefixCode.encode (.universalFunction t) = unary 5 (GorbowTermPrefixCode.encode t))

def FormulaConstructors : Prop := ∀ n : Nat,
  (∀ t u : Term n, GorbowFormulaPrefixCode.encode (.equal t u) = binary 0 (GorbowTermPrefixCode.encode t) (GorbowTermPrefixCode.encode u)) ∧
  (∀ t : Term n, GorbowFormulaPrefixCode.encode (.universalRelation t) = unary 1 (GorbowTermPrefixCode.encode t)) ∧
  (∀ t : Term n, GorbowFormulaPrefixCode.encode (.agent t) = unary 2 (GorbowTermPrefixCode.encode t)) ∧
  (∀ t : Term n, GorbowFormulaPrefixCode.encode (.knowledgeAll t) = unary 3 (GorbowTermPrefixCode.encode t)) ∧
  (∀ t u : Term n, GorbowFormulaPrefixCode.encode (.knowledge t u) = binary 4 (GorbowTermPrefixCode.encode t) (GorbowTermPrefixCode.encode u)) ∧
  (∀ t : Term n, GorbowFormulaPrefixCode.encode (.truth t) = unary 5 (GorbowTermPrefixCode.encode t)) ∧
  (∀ φ : Formula n, GorbowFormulaPrefixCode.encode (.neg φ) = unary 6 (GorbowFormulaPrefixCode.encode φ)) ∧
  (∀ φ ψ : Formula n, GorbowFormulaPrefixCode.encode (.imp φ ψ) = binary 7 (GorbowFormulaPrefixCode.encode φ) (GorbowFormulaPrefixCode.encode ψ)) ∧
  (∀ φ ψ : Formula n, GorbowFormulaPrefixCode.encode (.conj φ ψ) = binary 8 (GorbowFormulaPrefixCode.encode φ) (GorbowFormulaPrefixCode.encode ψ)) ∧
  (∀ φ ψ : Formula n, GorbowFormulaPrefixCode.encode (.disj φ ψ) = binary 9 (GorbowFormulaPrefixCode.encode φ) (GorbowFormulaPrefixCode.encode ψ)) ∧
  (∀ φ : Formula (n+1), GorbowFormulaPrefixCode.encode (.all φ) = unary 10 (GorbowFormulaPrefixCode.encode φ)) ∧
  (∀ φ : Formula (n+1), GorbowFormulaPrefixCode.encode (.ex φ) = unary 11 (GorbowFormulaPrefixCode.encode φ))

def NumeralCalibration : Prop := ∀ n k : Nat,
  GorbowTermPrefixCode.encode (Term.numeral k : Term n) = numeral k

def NumericInjection : Prop :=
  (∀ n : Nat, Function.Injective (@termNumber n)) ∧
  (∀ n : Nat, Function.Injective (@formulaNumber n))

def UniformPrograms : Prop := Primrec variableCode ∧
  Primrec (fun p : Nat × List Nat => unary p.1 p.2) ∧
  Primrec (fun p : Nat × List Nat × List Nat => binary p.1 p.2.1 p.2.2) ∧
  Primrec numeral ∧ Primrec number

def Target : Prop := TermConstructors ∧ FormulaConstructors ∧ NumeralCalibration ∧ NumericInjection ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowCodeConstructors
