module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.StatementChecks
public import LogicLineages.ComputabilityKnowledge.GorbowSyntaxValidation
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations List.Vector
open HistoryRuleSuffix
/-- Fresh validator candidate, not identification with any selected validity leaf. -/
def kind : Program 2 := applyOne (HistoryDecoder.decoder false) (.projection 0)
def context : Program 2 := applyOne (HistoryDecoder.decoder true) (.projection 0)
def task (k : Nat) (n : Program 2) : Program 2 := applyTwo HistoryCodec.pair (constant 2 k) n
def singleton (a : Program 2) : Program 2 := applyTwo HistoryCodec.cons a (constant 2 0)
def double (a : Program 2) : Program 2 := applyTwo HistoryCodec.cons a (singleton a)
def success (xs : Program 2) : Program 2 := applyOne .succ xs
/-- Equality case: choose's zero arm is failure of the equality test. -/
def whenEqual (x : Program 2) (k : Nat) (yes no : Program 2) : Program 2 :=
 choose (applyTwo equalCode x (constant 2 k)) no yes

def termBranch : Program 2 :=
 let t := (.projection 1 : Program 2)
 let one := success (singleton (task 0 context))
 let two := success (double (task 0 context))
 whenEqual t 0 (success (singleton (task 2 context)))
  (whenEqual t 1 (constant 2 1)
   (whenEqual t 2 one (whenEqual t 5 one
    (whenEqual t 3 two (whenEqual t 4 two (constant 2 0))))))
def formulaBranch : Program 2 :=
 let t := (.projection 1 : Program 2)
 let oneTerm := success (singleton (task 0 context))
 let twoTerm := success (double (task 0 context))
 let oneFormula := success (singleton (task 1 context))
 let twoFormula := success (double (task 1 context))
 let binder := success (singleton (task 1 (applyOne .succ context)))
 whenEqual t 0 twoTerm (whenEqual t 4 twoTerm
  (whenEqual t 1 oneTerm (whenEqual t 2 oneTerm (whenEqual t 3 oneTerm (whenEqual t 5 oneTerm
   (whenEqual t 6 oneFormula
    (whenEqual t 7 twoFormula (whenEqual t 8 twoFormula (whenEqual t 9 twoFormula
     (whenEqual t 10 binder (whenEqual t 11 binder (constant 2 0))))))))))))
/-- difference(token,n)=n-token: positive exactly when token<n. -/
def indexBranch : Program 2 :=
 choose (applyTwo HistoryCodec.difference (.projection 1) context) (constant 2 0) (constant 2 1)
def expandCode : Program 2 :=
 whenEqual kind 0 termBranch (whenEqual kind 1 formulaBranch
  (whenEqual kind 2 indexBranch (constant 2 0)))

/-- State uses original Option(List Task) encoding: NONE=0, SOME xs=succ(code xs). -/
def stack : Program 2 := applyOne HistoryCodec.predecessor (.projection 0)
def headTask : Program 2 := applyOne HistoryLookup.head stack
def restTasks : Program 2 := applyOne HistoryLookup.tail stack
def expanded : Program 2 := applyTwo expandCode headTask (.projection 1)
def appended : Program 2 := applyTwo HistoryAppend.append
 (applyOne HistoryCodec.predecessor expanded) restTasks
def stepCode : Program 2 :=
 choose (.projection 0) (constant 2 0)
  (choose stack (constant 2 0)
   (choose expanded (constant 2 0) (success appended)))

def expandCall {ctx : Nat} (tag : Nat) (t token : Term ctx) : Term ctx := call tag (t ::ᵥ token ::ᵥ nil)
def stepCall {ctx : Nat} (tag : Nat) (s token : Term ctx) : Term ctx := call tag (s ::ᵥ token ::ᵥ nil)
def taskCall {ctx : Nat} (ptag : Nat) (k : Nat) (n : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag (Term.numeral k) n
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep
