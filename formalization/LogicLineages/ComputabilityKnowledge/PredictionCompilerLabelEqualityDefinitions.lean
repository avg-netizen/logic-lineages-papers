module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerTapeSupportDefinitions
@[expose] public section
/-! Actual finite-domain equality tests for compiler labels. All function
fields are compared on the explicit five-element store enumeration; no
classical equality oracle is used in these algorithms. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerLabelEquality
open Turing Turing.PartrecToTM2 PredictionCompilerSupport PredictionCompilerTapeSupport

def sameStore {β : Type} [DecidableEq β] (f g : Store → β) : Bool :=
  symbols.all (fun s => decide (f s = g s))

def sameStore₂ {β : Type} [DecidableEq β] (f g : Store → Store → β) : Bool :=
  symbols.all (fun s => sameStore (f s) (g s))

def stackEq : StackStatement → StackStatement → Bool
  | .push k f q, .push j g r => decide (k = j) && sameStore f g && stackEq q r
  | .peek k f q, .peek j g r => decide (k = j) && sameStore₂ f g && stackEq q r
  | .pop k f q, .pop j g r => decide (k = j) && sameStore₂ f g && stackEq q r
  | .load f q, .load g r => sameStore f g && stackEq q r
  | .branch f q₁ q₂, .branch g r₁ r₂ => sameStore f g && stackEq q₁ r₁ && stackEq q₂ r₂
  | .goto f, .goto g => sameStore f g
  | .halt, .halt => true
  | _, _ => false

def actionEq {k : K'} : TM2to1.StAct K' StackAlphabet Store k → TM2to1.StAct K' StackAlphabet Store k → Bool
  | .push f, .push g => sameStore f g
  | .peek f, .peek g => sameStore₂ f g
  | .pop f, .pop g => sameStore₂ f g
  | _, _ => false

def labelEq : TapeLabel → TapeLabel → Bool
  | .normal l, .normal m => decide (l = m)
  | .ret q, .ret r => stackEq q r
  | .go k a q, .go j b r =>
    if h : k = j then actionEq a (h.symm ▸ b) && stackEq q r else false
  | _, _ => false

end LogicLineages.ComputabilityKnowledge.PredictionCompilerLabelEquality
