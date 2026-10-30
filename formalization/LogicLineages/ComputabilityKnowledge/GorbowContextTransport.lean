module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedBinding
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaPrefixCode

@[expose] public section

/-! Literal recontextualization, preserving all numeric variable names and raw
syntax. Unlike canonical selection this never renames a free variable. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowContextTransport
open GorbowSyntax

def term {n : Nat} (m : Nat) : Term n → Option (Term m)
  | .var i => if h : i.val<m then some (.var ⟨i.val,h⟩) else none
  | .zero => some .zero
  | .succ t => (term m t).map .succ
  | .add t u => do let t' ← term m t; let u' ← term m u; pure (.add t' u')
  | .mul t u => do let t' ← term m t; let u' ← term m u; pure (.mul t' u')
  | .universalFunction t => (term m t).map .universalFunction

def formula : {n : Nat} → (m : Nat) → Formula n → Option (Formula m)
  | _, m, .equal t u => do let t' ← term m t; let u' ← term m u; pure (.equal t' u')
  | _, m, .universalRelation t => (term m t).map .universalRelation
  | _, m, .agent t => (term m t).map .agent
  | _, m, .knowledgeAll t => (term m t).map .knowledgeAll
  | _, m, .knowledge t u => do let t' ← term m t; let u' ← term m u; pure (.knowledge t' u')
  | _, m, .truth t => (term m t).map .truth
  | _, m, .neg φ => (formula m φ).map .neg
  | _, m, .imp φ ψ => do let φ' ← formula m φ; let ψ' ← formula m ψ; pure (.imp φ' ψ')
  | _, m, .conj φ ψ => do let φ' ← formula m φ; let ψ' ← formula m ψ; pure (.conj φ' ψ')
  | _, m, .disj φ ψ => do let φ' ← formula m φ; let ψ' ← formula m ψ; pure (.disj φ' ψ')
  | _, m, .all φ => (formula (m+1) φ).map .all
  | _, m, .ex φ => (formula (m+1) φ).map .ex
end LogicLineages.ComputabilityKnowledge.GorbowContextTransport
