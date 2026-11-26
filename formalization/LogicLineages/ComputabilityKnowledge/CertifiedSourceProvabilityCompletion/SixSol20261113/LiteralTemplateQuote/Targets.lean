module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralTemplateQuote.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralTemplateQuote.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
/-- All runtime vectors; exact ORIGINAL syntax after numeral substitution,
not a numeral for the semantic value of the template. -/
def NativeCalibration : Prop := ∀ k (t : Term k) (values : List.Vector Nat k),
 evaluate (templateQuote t) values = Encodable.encode
  (GorbowTermPrefixCode.encode (GorbowSubstitution.substitute
   (fun i => (Term.numeral (values.get i) : Term 0)) t))
/-- Actual installed template AST, internally arbitrary runtime values.
Exactly one term task is consumed; no native-calibration premise. -/
def InternalScan : Prop := ∀ k (t : Term k) n (p : Program n)
 (qtag stag ptag ctag atag : Nat),
 (nodes p)[qtag]? = some ⟨k,templateQuote t⟩ →
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (values : List.Vector (Term ctx) k) (binder rest : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxScan.scanCall stag
   (HistoryLookup.consCall ctag (LiteralNumeralPrefix.termTask ptag binder) rest)
   (quoteCall qtag values)) (.succ rest)))
/-- Arbitrary suffix continuation in the same actual scanner. Syntax only:
no computation certification, producer correctness or HB3 is asserted. -/
def InternalContinuation : Prop := ∀ k (t : Term k) n (p : Program n)
 (qtag stag ptag ctag atag : Nat),
 (nodes p)[qtag]? = some ⟨k,templateQuote t⟩ →
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (values : List.Vector (Term ctx) k) (binder rest suffix : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxScan.scanCall stag
   (HistoryLookup.consCall ctag (LiteralNumeralPrefix.termTask ptag binder) rest)
   (HistoryAppend.appendCall atag (quoteCall qtag values) suffix))
   (LiteralSyntaxScan.scanCall stag rest suffix)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralTemplateQuote.Targets
