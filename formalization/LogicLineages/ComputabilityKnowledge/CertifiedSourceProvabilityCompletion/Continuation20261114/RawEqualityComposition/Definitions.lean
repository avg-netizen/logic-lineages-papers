module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawLogicalCoreRetention.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityComposition
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- Exact actual common checker: RightReplace(SuccReplace(Reflexivity(old))). -/
structure Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) extends
 toRight : RawRightReplaceCertificate.Installation p (RawCumulativeLogical.logical old) a x where
 oldTag : Nat
 reflexivityTag : Nat
 lengthTag : Nat
 rightTag : Nat
 dropTag : Nat
 lookupTag : Nat
 mpTag : Nat
 hold : (nodes p)[oldTag]? = some ⟨1,RawCumulativeLogical.logical old⟩
 hreflexivity : (nodes p)[reflexivityTag]? = some ⟨1,RawReflexivity.lineConstructor⟩
 hlength : (nodes p)[lengthTag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩
 hright : (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩
 hdrop : (nodes p)[dropTag]? = some ⟨2,HistoryLookup.drop⟩
 hlookup : (nodes p)[lookupTag]? = some ⟨2,HistoryLookup.lookup⟩
 hmp : (nodes p)[mpTag]? = some ⟨4,LiteralRawMP.constructor⟩
def eqRaw {ctx : Nat} (c a : Nat) (t u : Term ctx) : Term ctx :=
 RawSuccReplace.binaryValue c a 0 t u
def reflexivityCertificate {ctx : Nat} (c q : Nat) (t : Term ctx) : Term ctx :=
 RawCumulativeLogical.certificate c q t
/-- Two actual canonical MPs implement t=u, t=v ⊢ u=v using original tag12. -/
def transportCertificate {ctx : Nat} (m q c a : Nat) (t u v first second : Term ctx) : Term ctx :=
 LiteralMPRun.certificate m .zero (eqRaw c a u v)
  (LiteralMPRun.certificate m .zero
   (LiteralRawMP.implicationRaw a c (eqRaw c a t v) (eqRaw c a u v))
   (RawRightReplaceCertificate.certificate c q t u v) first) second
def symmetryCertificate {ctx : Nat} (m q ref c a : Nat) (t u cert : Term ctx) : Term ctx :=
 transportCertificate m q c a t u t cert (reflexivityCertificate c ref t)
def transitivityCertificate {ctx : Nat} (m q ref c a : Nat) (t u v first second : Term ctx) : Term ctx :=
 transportCertificate m q c a u t v (symmetryCertificate m q ref c a t u first) second
def accepted {ctx : Nat} (q c a : Nat) (index fuel t u cert : Term ctx) : Formula ctx :=
 .equal (LiteralCheckerAcceptance.coreCall q index fuel .zero
  (.add (eqRaw c a t u) (eqRaw c a t u)) cert) (.succ .zero)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityComposition
