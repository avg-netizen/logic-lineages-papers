module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
/-- All inputs, ORIGINAL Term numeral prefix code; not an externally bounded
family or a newly invented numeric syntax representation. -/
def NativeCalibration : Prop := ∀ value : Nat,
 evaluate numeralCode (value ::ᵥ nil) =
 Encodable.encode (GorbowTermPrefixCode.encode (Term.numeral value : Term 0))
/-- Internally arbitrary value/binder/remaining-task stack. Scanning the actual
numeral-code Program discharges precisely ONE term task and leaves the exact
remaining stack. No native numeral calibration or successful-parse premise. -/
def InternalScan : Prop := ∀ n (p : Program n) (ntag stag ptag ctag : Nat),
 (nodes p)[ntag]? = some ⟨1,numeralCode⟩ →
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 ∀ ctx (value binder rest : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxScan.scanCall stag
   (HistoryLookup.consCall ctag (termTask ptag binder) rest) (numeralCall ntag value)) (.succ rest)))
/-- Exact continuation on arbitrary raw suffix, not merely closed acceptance.
The same actual scanner and task stack are retained. This is syntax-building
infrastructure only, not computation quotation, producer correctness or HB3. -/
def InternalContinuation : Prop := ∀ n (p : Program n) (ntag stag ptag ctag atag : Nat),
 (nodes p)[ntag]? = some ⟨1,numeralCode⟩ →
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (value binder rest suffix : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxScan.scanCall stag (HistoryLookup.consCall ctag (termTask ptag binder) rest)
   (HistoryAppend.appendCall atag (numeralCall ntag value) suffix))
   (LiteralSyntaxScan.scanCall stag rest suffix)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.Targets
