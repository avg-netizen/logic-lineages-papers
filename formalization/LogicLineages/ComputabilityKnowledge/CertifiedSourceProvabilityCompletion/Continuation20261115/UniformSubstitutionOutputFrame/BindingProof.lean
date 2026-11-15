module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.InstallationProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.TransformProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.BindingProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix TransformProof
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
theorem outputInstalled {n : Nat} (p : Program n) (tag : Nat)
 (hf : (nodes p)[tag]? = some ⟨2,packedFrame⟩) :
 ∃ (otag : Nat), (nodes p)[otag]? = some ⟨2,outputFrame⟩ := by
 let g : Fin 2 → Program 2 := Fin.cases (applyOne (HistoryDecoder.decoder false) (.projection 1))
  (Fin.cases (applyTwo outputFrame (.projection 0) (applyOne (HistoryDecoder.decoder true) (.projection 1))) Fin.elim0)
 have harg := Equations.argumentChild p tag HistoryCodec.pair g hf 1
 let g1 : Fin 2 → Program 2 := Fin.cases (.projection 0) (Fin.cases (applyOne (HistoryDecoder.decoder true) (.projection 1)) Fin.elim0)
 exact ⟨tag+argumentTag HistoryCodec.pair g 1+1, Equations.functionChild p _ outputFrame g1 harg⟩
theorem packedBinding {n ctx : Nat} (p : Program n) (qtag ptag ftag ltag rtag : Nat)
 (hq : (nodes p)[qtag]? = some ⟨2,packedFrame⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hf : (nodes p)[ftag]? = some ⟨2,outputFrame⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩) (prefixCode state : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (frameCall qtag prefixCode state) (transformed ptag ftag ltag rtag prefixCode state))) := by
 let args := prefixCode ::ᵥ state ::ᵥ nil
 have hleft := unary p [] args (HistoryDecoder.decoder false) (.projection 1) state (call ltag (state ::ᵥ nil))
  (projection p [] args 1) (copies p [] (HistoryDecoder.decoder false) ltag hl _)
 have hright := unary p [] args (HistoryDecoder.decoder true) (.projection 1) state (call rtag (state ::ᵥ nil))
  (projection p [] args 1) (copies p [] (HistoryDecoder.decoder true) rtag hr _)
 have hout : Computes p [] packedFrame args (transformed ptag ftag ltag rtag prefixCode state) :=
  binary p [] args HistoryCodec.pair _ _ _ _ _ hleft
   (binary p [] args outputFrame (.projection 0) _ prefixCode _ _ (projection p [] args 0) hright (copies p [] outputFrame ftag hf _))
   (copies p [] HistoryCodec.pair ptag hp _)
 obtain ⟨h⟩ := hout qtag hq
 exact ⟨h.finish⟩
theorem projectTransform {n ctx : Nat} (p : Program n) (ptag ftag ltag rtag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩) (prefixCode packed : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call rtag (transformed ptag ftag ltag rtag prefixCode packed ::ᵥ nil))
   (frameCall ftag prefixCode (call rtag (packed ::ᵥ nil))))) :=
 HistoryLookup.DestructorProof.decoderCrossPair p rtag ptag true hr hp _ _
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.BindingProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.BindingProof
