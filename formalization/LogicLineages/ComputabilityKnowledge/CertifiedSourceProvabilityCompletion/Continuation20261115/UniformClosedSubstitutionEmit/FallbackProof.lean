module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.InternalAtomsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.FallbackProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open SixSol20261112.Fuel NamedArithmeticGraph InternalAtomsProof
/-- Original invalid/empty-state behavior emits the token, not failure. -/
theorem none {n ctx : Nat} (p : Program n) etag ctag
 (he : (nodes p)[etag]? = some ⟨3,emitCode⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (token raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (emitCall etag .zero token raw) (singletonValue ctag token))) := by
 let args := .zero ::ᵥ token ::ᵥ raw ::ᵥ nil
 have h : Computes p [] emitCode args (singletonValue ctag token) :=
  chooseZero p [] args (.projection 0) singletonCode _ _ (projection p [] args 0)
   (singleton p [] ctag hc .zero token raw)
 obtain ⟨hout⟩ := h etag he
 exact ⟨hout.finish⟩
theorem empty {n ctx : Nat} (p : Program n) etag ctag
 (he : (nodes p)[etag]? = some ⟨3,emitCode⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (token raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (emitCall etag (.succ .zero) token raw) (singletonValue ctag token))) := by
 let args := .succ .zero ::ᵥ token ::ᵥ raw ::ᵥ nil
 have hs : Computes p [] stackCode args .zero :=
  unary p [] args HistoryCodec.predecessor (.projection 0) (.succ .zero) .zero
   (projection p [] args 0) (predecessor p [] .zero)
 have h : Computes p [] emitCode args (singletonValue ctag token) :=
  choosePositive p [] args (.projection 0) singletonCode _ .zero _ (projection p [] args 0)
   (chooseZero p [] args stackCode singletonCode activeCode _ hs
    (singleton p [] ctag hc (.succ .zero) token raw))
 obtain ⟨hout⟩ := h etag he
 exact ⟨hout.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.FallbackProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.FallbackProof
