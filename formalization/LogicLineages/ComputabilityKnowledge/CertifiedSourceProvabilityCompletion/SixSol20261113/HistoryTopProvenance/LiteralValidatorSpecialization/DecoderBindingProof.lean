module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization.OccurrenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization.DecoderBindingProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

/-- Internal copy equality for a literal decoder at arbitrary code, supplied by
actual square-shell reconstruction rather than native evaluation. -/
theorem decoderValue {n ctx : Nat} (p : Program n) (ptag leftTag rightTag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hl : (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (right : Bool) (code : Term ctx) :
 Computes p [] (HistoryDecoder.decoder right) (code ::ᵥ nil)
   (HistoryDecoder.StepNormalProof.chosen right (call leftTag (code ::ᵥ nil)) (call rightTag (code ::ᵥ nil))) := by
 intro tag ht
 obtain ⟨h⟩ := HistoryTopProvenance.DecoderCopyProof.decodeAtReconstruction
   p ptag leftTag rightTag tag right hp hl hr ht code
 exact ⟨.base h⟩

/-- Literal line validation depends on its actual decoded context/raw fields
for EVERY raw line code. This is a proved AST equation, not an invariance
premise, and includes all payload/rule field encodings. -/
theorem lineDecoded {n ctx : Nat} (p : Program n) (ltag ftag ptag leftTag rightTag : Nat)
 (hline : (nodes p)[ltag]? = some ⟨1,LiteralSyntaxValidator.lineValidator⟩)
 (hf : (nodes p)[ftag]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hl : (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩) (line : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (.equal (LiteralSyntaxValidator.lineCall ltag line)
     (LiteralSyntaxValidator.formulaCall ftag (call leftTag (line ::ᵥ nil))
       (call leftTag (call rightTag (line ::ᵥ nil) ::ᵥ nil))))) := by
 let args := line ::ᵥ nil
 let lc := call leftTag (line ::ᵥ nil)
 let rest := call rightTag (line ::ᵥ nil)
 let raw := call leftTag (rest ::ᵥ nil)
 have hcontext : Computes p [] LiteralSyntaxValidator.lineContext args lc :=
   decoderValue p ptag leftTag rightTag hp hl hr false line
 have hrest : Computes p [] (HistoryDecoder.decoder true) args rest :=
   decoderValue p ptag leftTag rightTag hp hl hr true line
 have hraw : Computes p [] LiteralSyntaxValidator.lineRaw args raw :=
   unary p [] args (HistoryDecoder.decoder false) (HistoryDecoder.decoder true) rest raw
     hrest (decoderValue p ptag leftTag rightTag hp hl hr false rest)
 have hvalue : Computes p [] LiteralSyntaxValidator.lineValidator args
   (LiteralSyntaxValidator.formulaCall ftag lc raw) :=
   binary p [] args LiteralSyntaxValidator.formulaValidator LiteralSyntaxValidator.lineContext
     LiteralSyntaxValidator.lineRaw lc raw (LiteralSyntaxValidator.formulaCall ftag lc raw)
     hcontext hraw (copies p [] LiteralSyntaxValidator.formulaValidator ftag hf _)
 obtain ⟨h⟩ := hvalue ltag hline
 exact ⟨Hilbert.Local.finish h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization.DecoderBindingProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization.DecoderBindingProof
