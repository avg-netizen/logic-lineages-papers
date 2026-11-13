module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
/-- Exact ORIGINAL formula-prefix encoding of equality after numeral substitution
on all input vectors. This asserts syntax, not truth of the equality. -/
def NativeCalibration : Prop := ∀ k (t u : Term k) (values : List.Vector Nat k),
 evaluate (equalityQuote t u) values = Encodable.encode
  (GorbowFormulaPrefixCode.encode (.equal
   (GorbowSubstitution.substitute (fun i => (Term.numeral (values.get i) : Term 0)) t)
   (GorbowSubstitution.substitute (fun i => (Term.numeral (values.get i) : Term 0)) u)))
/-- Arbitrary internal runtime values: exactly one original formula task is
consumed. No validity, native-calibration or equality-truth premise. -/
def InternalScan : Prop := ∀ k (t u : Term k) n (p : Program n)
 (qtag stag ptag ctag atag : Nat),
 (nodes p)[qtag]? = some ⟨k,equalityQuote t u⟩ →
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (values : List.Vector (Term ctx) k) (binder rest : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxScan.scanCall stag
   (HistoryLookup.consCall ctag (formulaTask ptag binder) rest)
   (quoteCall qtag values)) (.succ rest)))
/-- Equality syntax followed by an arbitrary raw suffix resumes the SAME scanner
with the exact original rest stack. No certificate or HB3 assertion. -/
def InternalContinuation : Prop := ∀ k (t u : Term k) n (p : Program n)
 (qtag stag ptag ctag atag : Nat),
 (nodes p)[qtag]? = some ⟨k,equalityQuote t u⟩ →
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (values : List.Vector (Term ctx) k) (binder rest suffix : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxScan.scanCall stag
   (HistoryLookup.consCall ctag (formulaTask ptag binder) rest)
   (HistoryAppend.appendCall atag (quoteCall qtag values) suffix))
   (LiteralSyntaxScan.scanCall stag rest suffix)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote.Targets
