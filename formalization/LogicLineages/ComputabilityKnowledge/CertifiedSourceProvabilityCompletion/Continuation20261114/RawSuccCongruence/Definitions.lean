module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeLogical.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccCongruence
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- Literal common checker interface for two actual canonical MP operations.
No acceptance/proof premise is hidden in these structural node lookups. -/
structure Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) extends
 RawCumulativeLogical.CertificateInstallation p old a x where
 replaceTag : Nat
 lengthTag : Nat
 rightTag : Nat
 dropTag : Nat
 lookupTag : Nat
 mpTag : Nat
 hreplace : (nodes p)[replaceTag]? = some ⟨2,RawSuccReplace.lineConstructor⟩
 hlength : (nodes p)[lengthTag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩
 hright : (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩
 hdrop : (nodes p)[dropTag]? = some ⟨2,HistoryLookup.drop⟩
 hlookup : (nodes p)[lookupTag]? = some ⟨2,HistoryLookup.lookup⟩
 hmp : (nodes p)[mpTag]? = some ⟨4,LiteralRawMP.constructor⟩
def inputRaw {ctx : Nat} (ctag atag : Nat) (t u : Term ctx) : Term ctx :=
 RawSuccReplace.binaryValue ctag atag 0 t u
def selfRaw {ctx : Nat} (ctag atag : Nat) (t : Term ctx) : Term ctx :=
 RawReflexivity.equalityValue ctag atag (RawSuccReplace.succValue ctag t)
def outputRaw {ctx : Nat} (ctag atag : Nat) (t u : Term ctx) : Term ctx :=
 RawSuccReplace.binaryValue ctag atag 0 (RawSuccReplace.succValue ctag t) (RawSuccReplace.succValue ctag u)
def intermediateRaw {ctx : Nat} (ctag atag : Nat) (t u : Term ctx) : Term ctx :=
 LiteralRawMP.implicationRaw atag ctag (selfRaw ctag atag t) (outputRaw ctag atag t u)
def firstCertificate {ctx : Nat} (mpTag replaceTag ctag atag : Nat) (t u cert : Term ctx) : Term ctx :=
 LiteralMPRun.certificate mpTag .zero (intermediateRaw ctag atag t u)
  (RawSuccReplaceCertificate.certificate ctag replaceTag t u) cert
def certificate {ctx : Nat} (mpTag replaceTag reflexivityTag ctag atag : Nat) (t u cert : Term ctx) : Term ctx :=
 LiteralMPRun.certificate mpTag .zero (outputRaw ctag atag t u)
  (firstCertificate mpTag replaceTag ctag atag t u cert)
  (RawCumulativeLogical.certificate ctag reflexivityTag (RawSuccReplace.succValue ctag t))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccCongruence
