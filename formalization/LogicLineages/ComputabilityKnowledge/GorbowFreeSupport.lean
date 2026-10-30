module

public import LogicLineages.ComputabilityKnowledge.GorbowSyntax
public import Mathlib.Data.Finset.Card

@[expose] public section

/-! Actual free-variable sets in the full language. Ambient context size is
separate from the number or designated names of free variables. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowFreeSupport
open GorbowSyntax

def termSupport {n : Nat} : Term n → Finset Nat
  | .var i => {i.val}
  | .zero => ∅
  | .succ t | .universalFunction t => termSupport t
  | .add t u | .mul t u => termSupport t ∪ termSupport u

def unbind (s : Finset Nat) : Finset Nat := (s.erase 0).image Nat.pred

def formulaSupport : {n : Nat} → Formula n → Finset Nat
  | _, .equal t u | _, .knowledge t u => termSupport t ∪ termSupport u
  | _, .universalRelation t | _, .agent t | _, .knowledgeAll t | _, .truth t => termSupport t
  | _, .neg φ => formulaSupport φ
  | _, .imp φ ψ | _, .conj φ ψ | _, .disj φ ψ => formulaSupport φ ∪ formulaSupport ψ
  | _, .all φ | _, .ex φ => unbind (formulaSupport φ)

def PreciselyFree {m : Nat} (n : Nat) (φ : Formula m) : Prop := (formulaSupport φ).card = n

def FreeNames {m : Nat} (s : Finset Nat) (φ : Formula m) : Prop := formulaSupport φ = s
end LogicLineages.ComputabilityKnowledge.GorbowFreeSupport
