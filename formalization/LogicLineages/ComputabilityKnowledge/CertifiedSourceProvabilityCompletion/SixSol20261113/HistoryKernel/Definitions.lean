module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.StatementChecks

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel
open GorbowPRProgram GorbowSyntax GorbowPRDefiningEquations List.Vector
open HistoryRuleSuffix

/-- Explicit original State transition construction. No old opaque kernel AST
is identified with this Program. Inputs [state,index,fuel]. -/
def stateOption : Program 3 := applyOne (HistoryDecoder.decoder false) (.projection 0)
def stateLines : Program 3 := applyOne (HistoryDecoder.decoder true) (.projection 0)
def currentLine : Program 3 := applyOne HistoryLookup.head stateLines
def remainingLines : Program 3 := applyOne HistoryLookup.tail stateLines
def historyPayload : Program 3 := applyOne HistoryCodec.predecessor stateOption

def dispatcherArguments : Fin 4 → Program 3 :=
  Fin.cases (.projection 1) (Fin.cases (.projection 2)
    (Fin.cases historyPayload (Fin.cases currentLine Fin.elim0)))
def checkedLine (valid logical arithmetic : Program 1) (axiomProgram : Program 3) : Program 3 :=
  .composition (HistoryDispatcher.lineDispatcher valid logical arithmetic axiomProgram) dispatcherArguments
/-- Equality to ONE is essential: arbitrary internal native leaf outputs are
not assumed to have Boolean range. -/
def acceptedTest (valid logical arithmetic : Program 1) (axiomProgram : Program 3) : Program 3 :=
  applyTwo equalCode (checkedLine valid logical arithmetic axiomProgram) (constant 3 1)

def lineContext : Program 3 := applyOne (HistoryDecoder.decoder false) currentLine
def lineRaw : Program 3 := applyOne (HistoryDecoder.decoder false)
  (applyOne (HistoryDecoder.decoder true) currentLine)
def entry : Program 3 := applyTwo HistoryCodec.pair lineContext lineRaw
def extendedHistory : Program 3 := applyTwo HistoryCodec.cons entry historyPayload
def someExtendedHistory : Program 3 := applyOne .succ extendedHistory

def acceptedOption (valid logical arithmetic : Program 1) (axiomProgram : Program 3) : Program 3 :=
  choose (acceptedTest valid logical arithmetic axiomProgram) (constant 3 0) someExtendedHistory
/-- NONE remains NONE; no zero-default successful history. -/
def nextOption (valid logical arithmetic : Program 1) (axiomProgram : Program 3) : Program 3 :=
  choose stateOption (constant 3 0) (acceptedOption valid logical arithmetic axiomProgram)
def nextState (valid logical arithmetic : Program 1) (axiomProgram : Program 3) : Program 3 :=
  applyTwo HistoryCodec.pair (nextOption valid logical arithmetic axiomProgram) remainingLines
/-- Empty remaining line list is a genuine stuttering transition. -/
def kernel (valid logical arithmetic : Program 1) (axiomProgram : Program 3) : Program 3 :=
  choose stateLines (.projection 0) (nextState valid logical arithmetic axiomProgram)

def pairCall {ctx : Nat} (tag : Nat) (a b : Term ctx) : Term ctx := call tag (a ::ᵥ b ::ᵥ nil)
def kernelCall {ctx : Nat} (tag : Nat) (state index fuel : Term ctx) : Term ctx :=
  call tag (state ::ᵥ index ::ᵥ fuel ::ᵥ nil)
def activeState {ctx : Nat} (pairTag consTag : Nat) (history line rest : Term ctx) : Term ctx :=
  pairCall pairTag (.succ history) (HistoryLookup.consCall consTag line rest)

def stepSuffix {ctx : Nat} (ktag atag ptag ctag : Nat) (index fuel h tail line rest out : Term ctx) : Formula ctx :=
  .imp (.equal (kernelCall ktag (activeState ptag ctag h line rest) index fuel)
      (pairCall ptag (.succ out) rest))
    (.equal (kernelCall ktag (activeState ptag ctag (HistoryAppend.appendCall atag h tail) line rest) index fuel)
      (pairCall ptag (.succ (HistoryAppend.appendCall atag out tail)) rest))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel
