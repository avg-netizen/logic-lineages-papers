module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.StatementChecks

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRuleSuffix
open GorbowPRProgram GorbowSyntax GorbowPRDefiningEquations List.Vector

/-- Literal constants; no opaque PR witness. -/
def constant (arity : Nat) : Nat → Program arity
  | 0 => SixSol20261112.Fuel.zeroProgram arity
  | k+1 => .composition .succ (fun _ => constant arity k)
def applyOne {n : Nat} (f : Program 1) (a : Program n) : Program n :=
  .composition f (fun _ => a)
def applyTwo {n : Nat} (f : Program 2) (a b : Program n) : Program n :=
  .composition f (Fin.cases a (Fin.cases b Fin.elim0))
def choose {n : Nat} (test yesZero noPositive : Program n) : Program n :=
  .composition HistoryCodec.select (Fin.cases test (Fin.cases yesZero (Fin.cases noPositive Fin.elim0)))
/-- Boolean equality using both actual truncated differences. -/
def equalCode : Program 2 :=
  choose HistoryCodec.difference
    (choose (applyTwo HistoryCodec.difference (.projection 1) (.projection 0))
      (constant 2 1) (constant 2 0)) (constant 2 0)
def conjunction {n : Nat} (a b : Program n) : Program n :=
  choose a (constant n 0) b
/-- Decode an Option Entry only under the surrounding successful-reference guard. -/
def entryPart {n : Nat} (right : Bool) (option : Program n) : Program n :=
  applyOne (HistoryDecoder.decoder right) (applyOne HistoryCodec.predecessor option)

/-- Inputs [context,raw,Option antecedent-implication,Option antecedent].
Exactly the original rule2 match and three field conditions, including missing
reference failure. Payload canonicality is supplied by the actual mpLine wrapper. -/
def mpBody : Program 4 :=
  let a : Program 4 := .projection 2
  let b : Program 4 := .projection 3
  let eqContextA := applyTwo equalCode (entryPart false a) (.projection 0)
  let eqContextB := applyTwo equalCode (entryPart false b) (.projection 0)
  let implication := applyTwo HistoryCodec.cons (constant 4 7)
    (applyTwo HistoryAppend.append (entryPart true b) (.projection 1))
  let eqFormula := applyTwo equalCode (entryPart true a) implication
  choose a (constant 4 0) (choose b (constant 4 0)
    (conjunction eqContextA (conjunction eqContextB eqFormula)))
/-- Inputs [context,raw,Option premise], exact original rule3 match/conditions. -/
def generalizeBody : Program 3 :=
  let a : Program 3 := .projection 2
  let eqContext := applyTwo equalCode (entryPart false a) (applyOne .succ (.projection 0))
  let universal := applyTwo HistoryCodec.cons (constant 3 10) (entryPart true a)
  let eqFormula := applyTwo equalCode (.projection 1) universal
  choose a (constant 3 0) (conjunction eqContext eqFormula)

/-- Actual canonical modus-ponens rule checker: [history,context,raw,r1,r2]. -/
def mpArguments : Fin 4 → Program 5 :=
  Fin.cases (.projection 1) (Fin.cases (.projection 2)
    (Fin.cases (applyTwo HistoryLookup.lookup (.projection 3) (.projection 0))
      (Fin.cases (applyTwo HistoryLookup.lookup (.projection 4) (.projection 0)) Fin.elim0)))
def mpCheck : Program 5 := .composition mpBody mpArguments
/-- Actual canonical generalization rule checker: [history,context,raw,r]. -/
def generalizeArguments : Fin 3 → Program 4 :=
  Fin.cases (.projection 1) (Fin.cases (.projection 2)
    (Fin.cases (applyTwo HistoryLookup.lookup (.projection 3) (.projection 0)) Fin.elim0))
def generalizeCheck : Program 4 := .composition generalizeBody generalizeArguments

def mpCall {ctx : Nat} (tag : Nat) (history context raw r1 r2 : Term ctx) : Term ctx :=
  call tag (history ::ᵥ context ::ᵥ raw ::ᵥ r1 ::ᵥ r2 ::ᵥ nil)
def generalizeCall {ctx : Nat} (tag : Nat) (history context raw r : Term ctx) : Term ctx :=
  call tag (history ::ᵥ context ::ᵥ raw ::ᵥ r ::ᵥ nil)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRuleSuffix
