module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.FoldProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.EmitterProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.ConstructorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph UniformClosedSubstitutionRawFold
open RelationalSyntaxDepthTransport.ConstructorStepTargets
/-- Actual constructor consumption, with pending task expansion and accumulated
literal output. The variable marker has its separate two-token branch. -/
theorem consume {n ctx : Nat} (p : Program n) (ftag ptag ctag stag etag atag xtag : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,foldCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hx : (nodes p)[xtag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (ctor : Constructor) (hmarker : ctor ≠ .term 0) (bound rest tokens out raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (foldCall ftag (HistoryLookup.consCall ctag (Term.numeral (token ctor)) tokens)
    (HistoryKernel.pairCall ptag (input ptag ctag ctor bound rest) out) raw)
   (foldCall ftag tokens
    (HistoryKernel.pairCall ptag (.succ (output ptag ctag atag ctor bound rest))
     (HistoryAppend.appendCall atag out (UniformClosedSubstitutionEmit.singletonValue ctag (Term.numeral (token ctor))))) raw))) := by
 obtain ⟨hrec⟩ := (StatementChecks.exactRawRecursion n p ftag ptag ctag stag etag atag
  hf hp hc hs he ha ctx (Term.numeral (token ctor)) tokens (input ptag ctag ctor bound rest) out raw).2
 obtain ⟨hstep⟩ := RelationalSyntaxDepthTransport.ConstructorStepProof.stepAt
  p stag xtag ptag ctag atag hs hx hp hc ha ctor bound rest
 obtain ⟨hemit⟩ := UniformSubstitutionChunkTransport.EmitterProof.constructor
  p etag ptag ctag he hp hc ctor hmarker bound rest raw
 have happ := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) atag
  (out ::ᵥ UniformClosedSubstitutionEmit.emitCall etag (input ptag ctag ctor bound rest) (Term.numeral (token ctor)) raw ::ᵥ nil)
  (out ::ᵥ UniformClosedSubstitutionEmit.singletonValue ctag (Term.numeral (token ctor)) ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .logical (.reflexive _)
   | succ i => cases i using Fin.cases with
     | zero => exact hemit
     | succ i => exact Fin.elim0 i)
 have hpair := HistoryIteratorSuffix.ReconstructionProof.pairCongruence
  (T := GorbowPRNumeralCalculation.Theory p) (G := []) ptag _ _ _ _ (.base hstep) (.base happ)
 exact ⟨Logic.trans _ _ _ hrec (FoldProof.stateCongruence ftag tokens _ _ raw hpair.finish)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.ConstructorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.ConstructorProof
