module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.InstallationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags SixSol20261113
open SixSol20261112.Fuel HistoryRuleSuffix
/-- The relational helper's lookup is already inside the original append AST.
No extension, retagging assumption, or new program membership is introduced. -/
theorem lookupInstalled {n : Nat} (p : Program n) (atag : Nat)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) :
 ∃ lookupTag, (nodes p)[lookupTag]? = some ⟨2,HistoryLookup.lookup⟩ := by
 let ttag := HistoryAppend.AppendEquationsProof.tableTag atag
 have ht := HistoryAppend.AppendEquationsProof.tableInstalled p atag ha
 let vtag := HistoryAppend.TableEquationsProof.valueTag ttag
 have hv := HistoryAppend.TableEquationsProof.valueInstalled p ttag ht
 have hrec := Equations.argumentChild p vtag HistoryCodec.cons HistoryAppend.valueArguments hv 1
 let rectag := vtag + argumentTag HistoryCodec.cons HistoryAppend.valueArguments 1
 have href := Equations.argumentChild p rectag HistoryCodec.predecessor
  (fun _ : Fin 1 => HistoryAppend.reference) hrec 0
 let reftag := rectag + argumentTag HistoryCodec.predecessor (fun _ : Fin 1 => HistoryAppend.reference) 0
 exact ⟨reftag+1,Equations.functionChild p reftag HistoryLookup.lookup HistoryAppend.referenceArguments href⟩

/-- All auxiliary relational tags are extracted at the SAME original registry.
The right decoder comes from scan; the left decoder is inside append's head. -/
theorem auxiliaryTags {n : Nat} (p : Program n) (stag atag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) :
 ∃ lengthTag lookupTag leftTag rightTag,
 (nodes p)[lengthTag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ ∧
 (nodes p)[lookupTag]? = some ⟨2,HistoryLookup.lookup⟩ ∧
 (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩ ∧
 (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩ := by
 obtain ⟨itag,lengthTag,ptag,rightTag,hi,hl,hp,hr⟩ := LiteralSyntaxScan.InstalledNodesProof.scanNodes p stag hs
 obtain ⟨lookupTag,hlookup⟩ := lookupInstalled p atag ha
 have hh := HistoryAppend.AppendEquationsProof.headInstalled p atag ha
 have hleft := Equations.functionChild p (atag+1) (HistoryDecoder.decoder false)
  (fun _ : Fin 1 => HistoryCodec.predecessor) hh
 exact ⟨lengthTag,lookupTag,atag+1+1,rightTag,hl,hlookup,hleft,hr⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.InstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.InstallationProof
