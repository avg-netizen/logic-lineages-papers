module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionRawFold.InstallationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionRawFold.BindingProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 HistoryRuleSuffix List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
theorem binding {n ctx : Nat} (p : Program n) ftag ptag itag ltag rtag
 (hf : (nodes p)[ftag]? = some ⟨3,foldCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hi : (nodes p)[itag]? = some ⟨3,UniformClosedSubstitutionFold.iterator⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (tokens state raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (foldCall ftag tokens state raw)
   (call rtag (UniformClosedSubstitutionFold.iterateCall itag (HistoryLengthOffset.lengthCall ltag tokens)
    (HistoryKernel.pairCall ptag tokens state) raw ::ᵥ nil)))) := by
 let args := tokens ::ᵥ state ::ᵥ raw ::ᵥ nil
 have hlen : Computes p [] (applyOne HistoryLengthOffset.lengthProgram (.projection 0)) args
  (HistoryLengthOffset.lengthCall ltag tokens) :=
  unary p [] args HistoryLengthOffset.lengthProgram (.projection 0) tokens _
   (projection p [] args 0) (copies p [] HistoryLengthOffset.lengthProgram ltag hl _)
 have hinit : Computes p [] initial args (HistoryKernel.pairCall ptag tokens state) :=
  binary p [] args HistoryCodec.pair (.projection 0) (.projection 1) tokens state _
   (projection p [] args 0) (projection p [] args 1) (copies p [] HistoryCodec.pair ptag hp _)
 let v := UniformClosedSubstitutionFold.iterateCall itag (HistoryLengthOffset.lengthCall ltag tokens)
  (HistoryKernel.pairCall ptag tokens state) raw
 have hpack : Computes p [] finalPacked args v := by
  apply compose p [] UniformClosedSubstitutionFold.iterator _ args
   (HistoryLengthOffset.lengthCall ltag tokens ::ᵥ HistoryKernel.pairCall ptag tokens state ::ᵥ raw ::ᵥ nil) v _
   (copies p [] UniformClosedSubstitutionFold.iterator itag hi _)
  intro i
  cases i using Fin.cases with
  | zero => exact hlen
  | succ i => cases i using Fin.cases with
    | zero => exact hinit
    | succ i => cases i using Fin.cases with
      | zero => exact projection p [] args 2
      | succ i => exact Fin.elim0 i
 have hfold : Computes p [] foldCode args (call rtag (v ::ᵥ nil)) :=
  unary p [] args (HistoryDecoder.decoder true) finalPacked v _ hpack
   (copies p [] (HistoryDecoder.decoder true) rtag hr _)
 obtain ⟨h⟩ := hfold ftag hf
 exact ⟨h.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionRawFold.BindingProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionRawFold.BindingProof
