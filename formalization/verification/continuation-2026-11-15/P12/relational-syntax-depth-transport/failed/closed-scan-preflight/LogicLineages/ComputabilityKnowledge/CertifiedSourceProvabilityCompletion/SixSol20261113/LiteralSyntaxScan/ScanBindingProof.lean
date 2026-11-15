module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.StateRecursionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.ScanBindingProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open LiteralSyntaxStep.StepSupportProof Iteration StateRecursionProof

/-- Exact operational binding to independently installed identical ASTs. No
native equality or canonical-image assumption enters the internal proof. -/
theorem binding {n ctx : Nat} (p : Program n) (stag itag ltag ptag rtag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,scanCode⟩)
 (hi : (nodes p)[itag]? = some ⟨2,iterator⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (tasks raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (scanCall stag tasks raw) (scanState itag ltag ptag rtag raw (.succ tasks)))) := by
 let args := tasks ::ᵥ raw ::ᵥ nil
 let initialValue := HistoryKernel.pairCall ptag raw (.succ tasks)
 let lengthValue := HistoryLengthOffset.lengthCall ltag raw
 let runValue := runCall itag lengthValue initialValue
 have hinitial : Computes p [] initial args initialValue :=
  binary p [] args HistoryCodec.pair (.projection 1) (applyOne .succ (.projection 0))
   raw (.succ tasks) initialValue (projection p [] args 1)
   (unary p [] args .succ (.projection 0) tasks (.succ tasks)
    (projection p [] args 0) (successor p [] tasks))
   (copies p [] HistoryCodec.pair ptag hp _)
 have hlength : Computes p [] (applyOne HistoryLengthOffset.lengthProgram (.projection 1)) args lengthValue :=
  unary p [] args HistoryLengthOffset.lengthProgram (.projection 1) raw lengthValue
   (projection p [] args 1) (copies p [] HistoryLengthOffset.lengthProgram ltag hl _)
 have hrun : Computes p [] finalState args runValue :=
  binary p [] args iterator (applyOne HistoryLengthOffset.lengthProgram (.projection 1)) initial
   lengthValue initialValue runValue hlength hinitial (copies p [] iterator itag hi _)
 have hscan : Computes p [] scanCode args (scanState itag ltag ptag rtag raw (.succ tasks)) :=
  unary p [] args (HistoryDecoder.decoder true) finalState runValue _ hrun
   (copies p [] (HistoryDecoder.decoder true) rtag hr _)
 obtain ⟨h⟩ := hscan stag hs
 exact ⟨Hilbert.Local.finish h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.ScanBindingProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.ScanBindingProof
