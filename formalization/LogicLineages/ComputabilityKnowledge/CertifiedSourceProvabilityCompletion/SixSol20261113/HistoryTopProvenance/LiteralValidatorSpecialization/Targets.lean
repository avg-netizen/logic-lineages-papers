module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof

def ActualFormulaOccurrence : Prop := ∀ (l a : Program 1) (x : Program 3)
 n (p : Program n) (itag : Nat),
 (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator
   (HistoryKernel.kernel LiteralSyntaxValidator.lineValidator l a x)⟩ →
 (nodes p)[formulaTag itag l a x]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩

/-- Original arbitrary-count target specialized only to the actual explicit
literal validator. The old nonzero existential witness is discharged using
internal Boolean range and literal paired-field binding. No additional
validity, parse-boundary, native-calibration or source-identity premise. -/
def InternalTopFormulaValidity : Prop := ∀ (l a : Program 1) (x : Program 3)
 n (p : Program n) (itag ptag ctag leftTag rightTag : Nat),
 (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator
   (HistoryKernel.kernel LiteralSyntaxValidator.lineValidator l a x)⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩ →
 (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
 ∀ ctx (count lines context raw tail remaining index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (conclusion itag ptag ctag (formulaTag itag l a x)
     count lines context raw tail remaining index fuel))

def InternalFullRunFormulaValidity : Prop := ∀ (l a : Program 1) (x : Program 3)
 n (p : Program n) (itag ptag ctag leftTag rightTag : Nat),
 (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator
   (HistoryKernel.kernel LiteralSyntaxValidator.lineValidator l a x)⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩ →
 (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
 ∀ ctx (lines context raw tail index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (conclusion itag ptag ctag (formulaTag itag l a x)
     lines lines context raw tail .zero index fuel))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization.Targets
