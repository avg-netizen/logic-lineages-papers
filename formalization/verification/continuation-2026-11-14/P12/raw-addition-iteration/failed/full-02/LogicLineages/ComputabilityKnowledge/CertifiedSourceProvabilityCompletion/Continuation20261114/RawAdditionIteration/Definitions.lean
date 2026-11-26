module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionComputation.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionIteration
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations List.Vector SixSol20261113 HistoryRuleSuffix
/-- Literal canonical MP and original singleton axiom ASTs, not evaluators. -/
def mp {n : Nat} (result imp ant : Program n) : Program n :=
 .composition LiteralRawMP.constructor (Fin.cases (constant n 0) (Fin.cases result (Fin.cases imp (Fin.cases ant Fin.elim0))))
def singleton {n : Nat} (line : Program n) : Program n := applyTwo HistoryCodec.cons line (constant n 0)
def eqRaw {n : Nat} (t u : Program n) : Program n := RawSuccReplace.binaryRaw 0 t u
def transport {n : Nat} (t u v first second : Program n) : Program n :=
 mp (eqRaw u v) (mp (RawSuccReplace.binaryRaw 7 (eqRaw t v) (eqRaw u v))
  (singleton (RawRightReplace.line t u v)) first) second
def symmetry {n : Nat} (t u cert : Program n) : Program n :=
 transport t u t cert (singleton (applyOne RawReflexivity.lineConstructor t))
def transitivity {n : Nat} (t u v first second : Program n) : Program n :=
 transport u t v (symmetry t u first) second
def congruence {n : Nat} (t u cert : Program n) : Program n :=
 mp (eqRaw (RawAddSucc.successorRaw t) (RawAddSucc.successorRaw u))
  (mp (RawSuccReplace.binaryRaw 7 (eqRaw (RawAddSucc.successorRaw t) (RawAddSucc.successorRaw t))
    (eqRaw (RawAddSucc.successorRaw t) (RawAddSucc.successorRaw u)))
   (singleton (RawSuccReplace.line t u)) cert)
  (singleton (applyOne RawReflexivity.lineConstructor (RawAddSucc.successorRaw t)))
def computation {n : Nat} (t u v cert : Program n) : Program n :=
 transitivity (RawAddSucc.additionRaw t (RawAddSucc.successorRaw u))
  (RawAddSucc.successorRaw (RawAddSucc.additionRaw t u)) (RawAddSucc.successorRaw v)
  (singleton (RawAddSucc.line t u)) (congruence (RawAddSucc.additionRaw t u) v cert)
def stateRaw {n : Nat} (u v cert : Program n) : Program n :=
 applyTwo HistoryCodec.pair u (applyTwo HistoryCodec.pair v cert)
def base : Program 1 := stateRaw (applyTwo HistoryCodec.cons (constant 1 1) (constant 1 0))
 (.projection 0) (singleton (RawAddZero.line (.projection 0)))
def currentNumeral : Program 2 := applyOne (HistoryDecoder.decoder false) (.projection 1)
def currentValue : Program 2 := applyOne (HistoryDecoder.decoder false)
 (applyOne (HistoryDecoder.decoder true) (.projection 1))
def currentCertificate : Program 2 := applyOne (HistoryDecoder.decoder true)
 (applyOne (HistoryDecoder.decoder true) (.projection 1))
/-- Inputs [fixed left raw term, prior state]. -/
def step : Program 2 := stateRaw (RawAddSucc.successorRaw currentNumeral)
 (RawAddSucc.successorRaw currentValue)
 (computation (.projection 0) currentNumeral currentValue currentCertificate)
/-- Inputs [count,fixed raw term], initial certificate is constructed internally. -/
def iterator : Program 2 := .recursion base (applyTwo step (.projection 2) (.projection 1))
/-- The exact result syntax: prepend count successor tokens to the fixed term. -/
def successorPrefix : Program 2 := .recursion (.projection 0)
 (RawAddSucc.successorRaw (.projection (1 : Fin 3)))
structure Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) extends
 toAddition : RawAdditionComputation.Installation p old a x where
 leftTag : Nat
 baseTag : Nat
 stepTag : Nat
 iteratorTag : Nat
 numeralTag : Nat
 prefixTag : Nat
 hleft : (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩
 hbase : (nodes p)[baseTag]? = some ⟨1,base⟩
 hstep : (nodes p)[stepTag]? = some ⟨2,step⟩
 hiterator : (nodes p)[iteratorTag]? = some ⟨2,iterator⟩
 hnumeral : (nodes p)[numeralTag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩
 hprefix : (nodes p)[prefixTag]? = some ⟨2,successorPrefix⟩
def unaryCall {ctx : Nat} (tag : Nat) (t : Term ctx) : Term ctx := call tag (t ::ᵥ nil)
def binaryCall {ctx : Nat} (tag : Nat) (t u : Term ctx) : Term ctx := call tag (t ::ᵥ u ::ᵥ nil)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionIteration
