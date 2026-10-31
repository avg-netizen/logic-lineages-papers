module

public import LogicLineages.ComputabilityKnowledge.OraclePiThreeDefinitions

@[expose] public section
/-! Explicit finite-oracle trace matrices for the existing certificate-search
jumps. A witness codes a certificate, a finite oracle answer list and a finite
positive-witness list. No jump or halting predicate occurs in these matrices. -/
namespace LogicLineages.ComputabilityKnowledge.OracleThirdJumpNormalForm
open OracleCertificate OracleUniversal

def numberList (n : Nat) : List Nat := (Encodable.decode n).getD []
def traceCertificate (w : Nat) : Nat := w.unpair.1
def traceAnswers (w : Nat) : List Nat := numberList w.unpair.2.unpair.1
def traceWitnesses (w : Nat) : List Nat := numberList w.unpair.2.unpair.2

def traceOracle (w q : Nat) : Nat := (traceAnswers w).getD q 0
def positiveWitness (w j : Nat) : Nat := (traceWitnesses w).getD j 0

def packTrace (c : Nat) (answers witnesses : List Nat) : Nat :=
  Nat.pair c (Nat.pair (Encodable.encode answers) (Encodable.encode witnesses))

def traceAccepts (q w : Nat) : Bool :=
  certificateTest (traceOracle w) (Nat.pair q (traceCertificate w)) == 0

def firstMatrix (q c : Nat) : Bool :=
  certificateTest OracleJump.zeroOracle (Nat.pair q c) == 0

def secondMatrix (q w challenge : Nat) : Bool :=
  traceAccepts q w &&
    if challenge.unpair.1 ≤ traceCertificate w then
      let j := challenge.unpair.1
      let answer := traceOracle w (nodeInput j)
      if answer = 1 then firstMatrix (nodeInput j) (positiveWitness w j)
      else (answer == 0) && !(firstMatrix (nodeInput j) challenge.unpair.2)
    else true

def thirdMatrix (q w challenge response : Nat) : Bool :=
  traceAccepts q w &&
    if challenge.unpair.1 ≤ traceCertificate w then
      let j := challenge.unpair.1
      let answer := traceOracle w (nodeInput j)
      if answer = 1 then secondMatrix (nodeInput j) (positiveWitness w j) challenge.unpair.2
      else (answer == 0) && !(secondMatrix (nodeInput j) challenge.unpair.2 response)
    else true

def thirdComplementMatrix (a : Nat × Nat × Nat × Nat) : Bool :=
  !(thirdMatrix a.1 a.2.1 a.2.2.1 a.2.2.2)

end LogicLineages.ComputabilityKnowledge.OracleThirdJumpNormalForm
