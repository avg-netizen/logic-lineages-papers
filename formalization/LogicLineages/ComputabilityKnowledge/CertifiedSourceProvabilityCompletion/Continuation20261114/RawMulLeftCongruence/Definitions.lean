module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulRightCongruence.Definitions
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftRetention.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftCongruence
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- Preserve the entire previously used logical AST beneath the new leaf. -/
abbrev previousLogical (old : Program 1) : Program 1 := RawMulRightReplace.logicalLeaf (RawMulRightCongruence.previousLogical old)
structure Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) extends
 toCertificate : RawMulLeftCertificate.Installation p (previousLogical old) a x where
 addLeftTag : Nat
 rightReplaceTag : Nat
 addRightTag : Nat
 cumulativeTag : Nat
 previousTag : Nat
 reflexivityTag : Nat
 lookupTag : Nat
 mpTag : Nat
 haddLeft : (nodes p)[addLeftTag]? = some ⟨1,RawMulRightCongruence.previousLogical old⟩
 hrightReplace : (nodes p)[rightReplaceTag]? = some ⟨1,RawRightReplace.logicalLeaf (RawCumulativeLogical.logical old)⟩
 haddRight : (nodes p)[addRightTag]? = some ⟨1,RawAddLeftCongruence.previousLogical old⟩
 hcumulative : (nodes p)[cumulativeTag]? = some ⟨1,RawCumulativeLogical.logical old⟩
 hprevious : (nodes p)[previousTag]? = some ⟨1,previousLogical old⟩
 hreflexivity : (nodes p)[reflexivityTag]? = some ⟨1,RawReflexivity.lineConstructor⟩
 hlookup : (nodes p)[lookupTag]? = some ⟨2,HistoryLookup.lookup⟩
 hmp : (nodes p)[mpTag]? = some ⟨4,LiteralRawMP.constructor⟩
def mulRaw {ctx : Nat} (c a : Nat) (t v : Term ctx) : Term ctx := RawMulLeftReplace.binaryValue c a 4 t v
def eqRaw {ctx : Nat} (c a : Nat) (t u : Term ctx) : Term ctx := RawMulLeftReplace.binaryValue c a 0 t u
def outputRaw {ctx : Nat} (c a : Nat) (t u v : Term ctx) : Term ctx := eqRaw c a (mulRaw c a v t) (mulRaw c a v u)
def selfRaw {ctx : Nat} (c a : Nat) (t v : Term ctx) : Term ctx := RawReflexivity.equalityValue c a (mulRaw c a v t)
def intermediateRaw {ctx : Nat} (c a : Nat) (t u v : Term ctx) : Term ctx :=
 LiteralRawMP.implicationRaw a c (selfRaw c a t v) (outputRaw c a t u v)
def certificate {ctx : Nat} (m q ref c a : Nat) (t u v input : Term ctx) : Term ctx :=
 LiteralMPRun.certificate m .zero (outputRaw c a t u v)
  (LiteralMPRun.certificate m .zero (intermediateRaw c a t u v)
   (RawMulLeftCertificate.certificate c q t u v) input)
  (RawCumulativeLogical.certificate c ref (mulRaw c a v t))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftCongruence
