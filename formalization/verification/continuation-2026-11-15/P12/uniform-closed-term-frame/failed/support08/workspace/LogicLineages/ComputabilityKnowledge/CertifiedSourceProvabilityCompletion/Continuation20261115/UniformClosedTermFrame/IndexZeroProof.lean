module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.IndexZeroProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPRDefiningEquations List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationalSyntaxDepthTransport LiteralRawMP.DispatcherSupportProof
/-- Actual difference orientation: token subtracted from zero always saturates. -/
theorem differenceRightZero {n ctx : Nat} (p : Program n) (dtag : Nat)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩) (token : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryDifference.differenceCall dtag token .zero) .zero)) := by
 obtain ⟨hz⟩ := HistoryDifference.ArithmeticProof.differenceSaturate n p dtag hd ctx .zero token
 have he := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) dtag
  (token ::ᵥ (.zero : Term ctx) ::ᵥ nil) (.add .zero token ::ᵥ .zero ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact Support.equalitySymmetry _ _ (zeroLeft token)
   | succ i => cases i using Fin.cases with
     | zero => exact .logical (.reflexive _)
     | succ i => exact Fin.elim0 i)
 exact ⟨Logic.trans _ _ _ he hz⟩
/-- No native arithmetic or token-image assumption: the actual original index
branch at bound zero rejects every arbitrary runtime token. -/
theorem expandZero {n ctx : Nat} (p : Program n) (etag ptag l r dtag : Nat)
 (he : (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩) (token : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxStep.expandCall etag (LiteralSyntaxStep.taskCall ptag 2 .zero) token) .zero)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let task : Term ctx := LiteralSyntaxStep.taskCall ptag 2 .zero
 obtain ⟨hk⟩ := HistoryLookup.DestructorProof.decoderCrossPair p l ptag false hl hp (Term.numeral (n := ctx) 2) .zero
 obtain ⟨hb⟩ := HistoryLookup.DestructorProof.decoderCrossPair p r ptag true hr hp (Term.numeral (n := ctx) 2) .zero
 have hc := Logic.callCongruence T dtag (token ::ᵥ call r (task ::ᵥ nil) ::ᵥ nil)
  (token ::ᵥ .zero ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .logical (.reflexive token)
   | succ i => cases i using Fin.cases with
     | zero => exact hb
     | succ i => exact Fin.elim0 i)
 obtain ⟨hz⟩ := differenceRightZero p dtag hd token
 have hdiff := Logic.trans _ _ _ hc hz
 obtain ⟨hout⟩ := ExpansionRuntimeProof.indexZero p [] l r dtag hl hr hd task token
  (Hilbert.Local.base hk) (Hilbert.Local.base hdiff) etag he
 exact ⟨hout.finish⟩
/-- Rejection propagates through the original cons-stack step, including every
malformed rest and every runtime token. -/
theorem stepZero {n ctx : Nat} (p : Program n) (stag etag ptag ctag l r dtag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩) (rest token : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxStep.stepCall stag
   (.succ (HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag 2 .zero) rest)) token) .zero)) := by
 obtain ⟨hz⟩ := expandZero p etag ptag l r dtag he hp hl hr hd token
 obtain ⟨hout⟩ := StepRejectionProof.stepReject p [] etag ctag he hc
  (LiteralSyntaxStep.taskCall ptag 2 .zero) rest token (Hilbert.Local.base hz) stag hs
 exact ⟨hout.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.IndexZeroProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.IndexZeroProof
