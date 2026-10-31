module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerSupportDefinitions
@[expose] public section
/-! Explicit support lists through the actual Mathlib TM2→TM1→TM0 compiler
chain. Working alphabets and encoded-stack input/output remain unchanged.
Lists are constructed by syntax recursion and finite products, not by choosing
representatives from Finsets. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerTapeSupport
open Turing Turing.ToPartrec Turing.PartrecToTM2 PredictionCompilerSupport
abbrev StackAlphabet (_ : K') := Γ'
abbrev Store := Option Γ'
abbrev TapeAlphabet := TM2to1.Γ' K' StackAlphabet
abbrev TapeLabel := TM2to1.Λ' K' StackAlphabet Λ' Store
abbrev StackStatement := TM2.Stmt StackAlphabet Λ' Store
abbrev TapeStatement := TM1.Stmt TapeAlphabet TapeLabel Store

def tapeMachine : TapeLabel → TapeStatement := TM2to1.tr tr

def stackStatementList : StackStatement → List TapeLabel
  | .push k f q => .go k (.push f) q :: .ret q :: stackStatementList q
  | .peek k f q => .go k (.peek f) q :: .ret q :: stackStatementList q
  | .pop k f q => .go k (.pop f) q :: .ret q :: stackStatementList q
  | .load _ q => stackStatementList q
  | .branch _ q₁ q₂ => stackStatementList q₁ ++ stackStatementList q₂
  | .goto _ => []
  | .halt => []

def tapeLabels (c : Code) (k : Cont') : List TapeLabel :=
  (supportList c k).flatMap (fun l => .normal l :: stackStatementList (tr l))

def tapeStatementList : TapeStatement → List TapeStatement
  | Q@(.move _ q) => Q :: tapeStatementList q
  | Q@(.write _ q) => Q :: tapeStatementList q
  | Q@(.load _ q) => Q :: tapeStatementList q
  | Q@(.branch _ q₁ q₂) => Q :: (tapeStatementList q₁ ++ tapeStatementList q₂)
  | Q@(.goto _) => [Q]
  | Q@(.halt) => [Q]

def tapeStatements (c : Code) (k : Cont') : List (Option TapeStatement) :=
  none :: (tapeLabels c k).flatMap (fun l => (tapeStatementList (tapeMachine l)).map some)

abbrev PostLabel := TM1to0.Λ' tapeMachine

def postLabels (c : Code) (k : Cont') : List PostLabel :=
  (tapeStatements c k).flatMap (fun q => symbols.map (fun s => (q, s)))

def postMachine : PostLabel → TapeAlphabet → Option (PostLabel × TM0.Stmt TapeAlphabet) :=
  TM1to0.tr tapeMachine

end LogicLineages.ComputabilityKnowledge.PredictionCompilerTapeSupport
