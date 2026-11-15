module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.FoldProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.EmitterProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.MarkerProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph UniformClosedSubstitutionRawFold
open RelationalSyntaxDepthTransport.ConstructorStepTargets
/-- The actual variable marker is consumed, its output suppressed, and its
original index task retained for the second token. -/
theorem consume {n ctx : Nat} (p : Program n) (ftag ptag ctag stag etag atag xtag : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,foldCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hx : (nodes p)[xtag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (bound rest tokens out raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (foldCall ftag (HistoryLookup.consCall ctag .zero tokens)
    (HistoryKernel.pairCall ptag (input ptag ctag (.term 0) bound rest) out) raw)
   (foldCall ftag tokens
    (HistoryKernel.pairCall ptag (.succ (output ptag ctag atag (.term 0) bound rest))
     (HistoryAppend.appendCall atag out (.zero))) raw))) := by
 obtain ⟨hrec⟩ := (StatementChecks.exactRawRecursion n p ftag ptag ctag stag etag atag
  hf hp hc hs he ha ctx .zero tokens (input ptag ctag (.term 0) bound rest) out raw).2
 obtain ⟨hstep⟩ := RelationalSyntaxDepthTransport.ConstructorStepProof.stepAt
  p stag xtag ptag ctag atag hs hx hp hc ha (.term 0) bound rest
 obtain ⟨hemit⟩ := UniformClosedSubstitutionEmit.NonIndexProof.marker
  p etag ptag ctag he hp hc bound rest raw
 have happ := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) atag
  (out ::ᵥ UniformClosedSubstitutionEmit.emitCall etag (input ptag ctag (.term 0) bound rest) .zero raw ::ᵥ nil)
  (out ::ᵥ .zero ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .logical (.reflexive _)
   | succ i => cases i using Fin.cases with
     | zero => exact hemit
     | succ i => exact Fin.elim0 i)
 have hpair := HistoryIteratorSuffix.ReconstructionProof.pairCongruence
  (T := GorbowPRNumeralCalculation.Theory p) (G := []) ptag _ _ _ _ (.base hstep) (.base happ)
 exact ⟨Logic.trans _ _ _ hrec (FoldProof.stateCongruence ftag tokens _ _ raw hpair.finish)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.MarkerProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.MarkerProof
