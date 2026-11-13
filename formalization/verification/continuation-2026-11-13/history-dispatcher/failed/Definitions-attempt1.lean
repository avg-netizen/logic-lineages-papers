module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRuleSuffix.StatementChecks

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher
open GorbowPRProgram GorbowSyntax GorbowPRDefiningEquations List.Vector
open HistoryRuleSuffix

/-- New literal dispatcher construction, not an identity claim about the old
opaque HistoryMachine kernel. The external leaves are history-independent. -/
def defaultLine : GorbowProofChecker.Line := (0,[],0,0,[],0,0)
def decodedLine (code : Nat) : GorbowProofChecker.Line := (Encodable.decode code).getD defaultLine
def withRule (r : Nat) (l : GorbowProofChecker.Line) : GorbowProofChecker.Line :=
  (GorbowProofChecker.context l,GorbowProofChecker.conclusion l,r,GorbowProofChecker.payload l)
def truth (b : Bool) : Nat := if b then 1 else 0

def validFunction (v : List.Vector Nat 1) : Nat :=
  let l := decodedLine v.head
  truth (GorbowSyntaxValidation.validFormula (GorbowProofChecker.context l) (GorbowProofChecker.conclusion l))
def logicalFunction (v : List.Vector Nat 1) : Nat :=
  truth (GorbowProofChecker.ruleCheck [] (withRule 0 (decodedLine v.head)))
def arithmeticFunction (v : List.Vector Nat 1) : Nat :=
  truth (GorbowProofChecker.ruleCheck [] (withRule 1 (decodedLine v.head)))
def axiomFunction (v : List.Vector Nat 3) : Nat :=
  let l := decodedLine v.tail.tail.head
  truth (GorbowTheoryChecker.axiomCheck
    (GorbowEnumeratedProvability.axiomCheck (Denumerable.ofNat GorbowEnumeratedProvability.Code v.head,v.tail.head))
    (GorbowProofChecker.context l) (GorbowProofChecker.conclusion l) (GorbowProofChecker.payload l))

def NativeLeaves (valid logical arithmetic : Program 1) (axiom : Program 3) : Prop :=
  (∀ v, evaluate valid v=validFunction v) ∧
  (∀ v, evaluate logical v=logicalFunction v) ∧
  (∀ v, evaluate arithmetic v=arithmeticFunction v) ∧
  (∀ v, evaluate axiom v=axiomFunction v)

/-- Inputs throughout the dispatcher are [index,fuel,history,encoded Line]. -/
def left (q : Program 4) : Program 4 := applyOne (HistoryDecoder.decoder false) q
def right (q : Program 4) : Program 4 := applyOne (HistoryDecoder.decoder true) q
def lineCode : Program 4 := .projection 3
def contextCode : Program 4 := left lineCode
def rawCode : Program 4 := left (right lineCode)
def ruleCode : Program 4 := left (right (right lineCode))
def payloadCode : Program 4 := right (right (right lineCode))
def payloadTag : Program 4 := left payloadCode
def payloadArgs : Program 4 := left (right payloadCode)
def ref1 : Program 4 := left (right (right payloadCode))
def ref2 : Program 4 := right (right (right payloadCode))
def zeroTest (q : Program 4) : Program 4 := applyTwo equalCode q (constant 4 0)
def commonGuard : Program 4 := conjunction (zeroTest payloadTag) (zeroTest payloadArgs)
def generalizeGuard : Program 4 := conjunction commonGuard (zeroTest ref2)

def mpArguments : Fin 5 → Program 4 :=
  Fin.cases (.projection 2) (Fin.cases contextCode (Fin.cases rawCode
    (Fin.cases ref1 (Fin.cases ref2 Fin.elim0))))
def generalizeArguments : Fin 4 → Program 4 :=
  Fin.cases (.projection 2) (Fin.cases contextCode (Fin.cases rawCode (Fin.cases ref1 Fin.elim0)))
def mpBranch : Program 4 := conjunction commonGuard (.composition mpCheck mpArguments)
def generalizeBranch : Program 4 := conjunction generalizeGuard (.composition generalizeCheck generalizeArguments)
def axiomArguments : Fin 3 → Program 4 :=
  Fin.cases (.projection 0) (Fin.cases (.projection 1) (Fin.cases lineCode Fin.elim0))
def ruleSelect (r : Nat) (yes no : Program 4) : Program 4 :=
  choose (applyTwo equalCode ruleCode (constant 4 r)) no yes

def ruleDispatcher (logical arithmetic : Program 1) (axiom : Program 3) : Program 4 :=
  ruleSelect 0 (applyOne logical lineCode)
    (ruleSelect 1 (applyOne arithmetic lineCode)
      (ruleSelect 2 mpBranch (ruleSelect 3 generalizeBranch
        (ruleSelect 4 (.composition axiom axiomArguments) (constant 4 0)))))
def lineDispatcher (valid logical arithmetic : Program 1) (axiom : Program 3) : Program 4 :=
  conjunction (applyOne valid lineCode) (ruleDispatcher logical arithmetic axiom)

def dispatcherCall {ctx : Nat} (tag : Nat) (index fuel history line : Term ctx) : Term ctx :=
  call tag (index ::ᵥ fuel ::ᵥ history ::ᵥ line ::ᵥ nil)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher
