module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralMPRun
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations List.Vector
open LiteralRawMP HistoryRunSplice HistoryLengthOffset

/-- Actual constructor call, not a native replacement or a selected SAME root. -/
def certificate {ctx : Nat} (mtag : Nat) (context raw imp ant : Term ctx) : Term ctx :=
  call mtag (context ::ᵥ raw ::ᵥ imp ::ᵥ ant ::ᵥ nil)

def trailingLine {ctx : Nat} (ltag ptag : Nat) (context raw ant : Term ctx) : Term ctx :=
  lineValue ptag context raw (lengthCall ltag ant)

def trailingLines {ctx : Nat} (ltag ptag ctag : Nat) (context raw ant : Term ctx) : Term ctx :=
  HistoryLookup.consCall ctag (trailingLine ltag ptag context raw ant) .zero

/-- Explicit actual validity leaf on the NEW MP line; it is not inferred from
native validity or from validity of either input certificate. -/
def newLineValid {ctx : Nat} (dispatcherTag ltag ptag : Nat)
    (v l a : Program 1) (x : Program 3) (context raw ant : Term ctx) : Formula ctx :=
  .equal (call (validityTag dispatcherTag v l a x)
    (trailingLine ltag ptag context raw ant ::ᵥ nil)) (.succ .zero)

/-- Newest-first successful output: new conclusion, antecedent history, then
implication history. The certificate order itself is implication then antecedent. -/
def outputState {ctx : Nat} (atag ptag ctag : Nat)
    (context phi psi tailI tailA : Term ctx) : Term ctx :=
  HistoryKernel.pairCall ptag
    (.succ (HistoryLookup.consCall ctag (HistoryKernel.pairCall ptag context psi)
      (joinedHistory atag ptag ctag context phi psi tailI tailA))) .zero
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralMPRun
