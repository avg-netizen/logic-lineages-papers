module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.StatementChecks
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryCertificateOperationsDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations List.Vector
open HistoryRuleSuffix HistoryRunSplice HistoryLengthOffset

/-- [context, encoded raw conclusion, implication reference]. The original
canonical payload is (0,[],r1,0), and rule tag is exactly 2. -/
def lineProgram : Program 3 :=
  applyTwo HistoryCodec.pair (.projection 0)
    (applyTwo HistoryCodec.pair (.projection 1)
      (applyTwo HistoryCodec.pair (constant 3 2)
        (applyTwo HistoryCodec.pair (constant 3 0)
          (applyTwo HistoryCodec.pair (constant 3 0)
            (applyTwo HistoryCodec.pair (.projection 2) (constant 3 0))))))
def lineArguments : Fin 3 → Program 4 :=
  Fin.cases (.projection 0) (Fin.cases (.projection 1)
    (Fin.cases (applyOne lengthProgram (.projection 3)) Fin.elim0))
def newLine : Program 4 := .composition lineProgram lineArguments
/-- [context, encoded raw conclusion, implication certificate, antecedent
certificate]. Exact original order; length is a genuine reference computation. -/
def constructor : Program 4 :=
  applyTwo HistoryAppend.append
    (applyTwo HistoryAppend.append (.projection 2) (.projection 3))
    (applyTwo HistoryCodec.cons newLine (constant 4 0))

def lineValue {ctx : Nat} (ptag : Nat) (context raw ref1 : Term ctx) : Term ctx :=
  HistoryKernel.pairCall ptag context (HistoryKernel.pairCall ptag raw
    (HistoryKernel.pairCall ptag (.succ (.succ .zero)) (HistoryKernel.pairCall ptag .zero
      (HistoryKernel.pairCall ptag .zero (HistoryKernel.pairCall ptag ref1 .zero)))))
def implicationRaw {ctx : Nat} (atag ctag : Nat) (phi psi : Term ctx) : Term ctx :=
  HistoryLookup.consCall ctag (Term.numeral 7) (HistoryAppend.appendCall atag phi psi)
def implicationEntry {ctx : Nat} (atag ptag ctag : Nat) (context phi psi : Term ctx) : Term ctx :=
  HistoryKernel.pairCall ptag context (implicationRaw atag ctag phi psi)
def antecedentEntry {ctx : Nat} (ptag : Nat) (context phi : Term ctx) : Term ctx :=
  HistoryKernel.pairCall ptag context phi
def implicationHistory {ctx : Nat} (atag ptag ctag : Nat) (context phi psi tail : Term ctx) : Term ctx :=
  HistoryLookup.consCall ctag (implicationEntry atag ptag ctag context phi psi) tail
def antecedentHistory {ctx : Nat} (ptag ctag : Nat) (context phi tail : Term ctx) : Term ctx :=
  HistoryLookup.consCall ctag (antecedentEntry ptag context phi) tail

def inputRuns {ctx : Nat} (itag atag ptag ctag : Nat)
    (context phi psi imp ant tailI tailA index fuel : Term ctx) : Formula ctx :=
  .conj
    (.equal (run itag ptag imp (.succ .zero) imp index fuel)
      (state ptag (.succ (implicationHistory atag ptag ctag context phi psi tailI)) .zero))
    (.equal (run itag ptag ant (.succ .zero) ant index fuel)
      (state ptag (.succ (antecedentHistory ptag ctag context phi tailA)) .zero))
def joinedHistory {ctx : Nat} (atag ptag ctag : Nat) (context phi psi tailI tailA : Term ctx) : Term ctx :=
  HistoryAppend.appendCall atag (antecedentHistory ptag ctag context phi tailA)
    (implicationHistory atag ptag ctag context phi psi tailI)
def references {ctx : Nat} (ltag atag ptag ctag rtag : Nat)
    (context phi psi ant tailI tailA : Term ctx) : Formula ctx :=
  .conj
    (.equal (HistoryLookup.lookupCall rtag (lengthCall ltag ant) (joinedHistory atag ptag ctag context phi psi tailI tailA))
      (.succ (implicationEntry atag ptag ctag context phi psi)))
    (.equal (HistoryLookup.lookupCall rtag .zero (joinedHistory atag ptag ctag context phi psi tailI tailA))
      (.succ (antecedentEntry ptag context phi)))

/-- Actual validity leaf child of the literal dispatcher, not a separate
extensional witness and not native validity reflection. -/
def validityTag (tag : Nat) (v l a : Program 1) (x : Program 3) : Nat :=
  tag + argumentTag HistoryCodec.select
    (Fin.cases (applyOne v HistoryDispatcher.lineCode)
      (Fin.cases (constant 4 0) (Fin.cases (HistoryDispatcher.ruleDispatcher l a x) Fin.elim0))) 0 + 1
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP
