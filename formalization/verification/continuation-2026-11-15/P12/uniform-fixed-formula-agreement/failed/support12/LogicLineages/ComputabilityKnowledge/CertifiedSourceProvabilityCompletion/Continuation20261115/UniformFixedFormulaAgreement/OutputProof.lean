module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.OutputProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph
noncomputable def rightCongruence {ctx : Nat} {T : Sentence → Prop} (tag : Nat)
 (left a b : Term ctx) (h : Derivation T (.equal a b)) :
 Derivation T (.equal (HistoryAppend.appendCall tag left a) (HistoryAppend.appendCall tag left b)) := by
 apply Logic.callCongruence T tag
 intro i
 cases i using Fin.cases with
 | zero => exact .logical (.reflexive _)
 | succ i => cases i using Fin.cases with
   | zero => exact h
   | succ i => exact Fin.elim0 i
/-- Suppressed marker followed by the emitted variable chunk: no arbitrary
right-empty identity is assumed. Original associativity and left-nil suffice. -/
theorem zeroThen {n ctx : Nat} (p : Program n) (atag ctag ltag rtag : Nat)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (out value : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryAppend.appendCall atag (HistoryAppend.appendCall atag out .zero) value)
   (HistoryAppend.appendCall atag out value))) := by
 obtain ⟨hassoc⟩ := LiteralSyntaxFrame.AppendProof.internalAppendAssociativity
  n p atag ctag ltag rtag ha hc hl hr ctx out .zero value
 obtain ⟨hnil⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx value
 exact ⟨Logic.trans _ _ _ hassoc (rightCongruence atag out _ value hnil)⟩
/-- Copied constructor token followed by the child output is exactly cons of
that token onto the child, inside the original arbitrary output accumulator. -/
theorem tokenThen {n ctx : Nat} (p : Program n) (atag ctag ltag rtag : Nat)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (out token value : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryAppend.appendCall atag
    (HistoryAppend.appendCall atag out (HistoryLookup.consCall ctag token .zero)) value)
   (HistoryAppend.appendCall atag out (HistoryLookup.consCall ctag token value)))) := by
 obtain ⟨hassoc⟩ := LiteralSyntaxFrame.AppendProof.internalAppendAssociativity
  n p atag ctag ltag rtag ha hc hl hr ctx out (HistoryLookup.consCall ctag token .zero) value
 obtain ⟨hcons⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx token .zero value
 obtain ⟨hnil⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx value
 have hcng := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) ctag
  (token ::ᵥ HistoryAppend.appendCall atag .zero value ::ᵥ nil)
  (token ::ᵥ value ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .logical (.reflexive _)
   | succ i => cases i using Fin.cases with
     | zero => exact hnil
     | succ i => exact Fin.elim0 i)
 exact ⟨Logic.trans _ _ _ hassoc (rightCongruence atag out _ _ (Logic.trans _ _ _ hcons hcng))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.OutputProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.OutputProof
