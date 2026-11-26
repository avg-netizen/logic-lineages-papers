module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Internal agreement with the ORIGINAL fixed-template substitution. The raw
replacement is arbitrary, subject only to the original closed-term validator.
No formula-dependent program membership or native-image premise is required. -/
def InternalAgreement : Prop := ∀ n (p : Program n)
 (ftag etag vtag fval stepTag stag ptag ctag atag dtag len q l r : Nat),
 (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩ →
 (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩ →
 (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ →
 (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩ →
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩ →
 (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ →
 (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩ →
 (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩ →
 (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩ →
 (nodes p)[fval]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩ →

 ∀ (f : Formula 1) ctx (replacement : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (Continuation20261114.RawReflexivityDispatcher.valid vtag replacement)
   (.equal (uniformValue ftag ptag ctag r f replacement)
    (FullFormulaInstantiation.instanceValue ctag atag f replacement))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.Targets
