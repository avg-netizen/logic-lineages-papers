module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.FormulaBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.LineBindingProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

theorem internalLineBinding : Targets.InternalLineBinding := by
 intro n p ltag vtag ptag hl hv hp ctx context raw payload
 let rest := HistoryKernel.pairCall ptag raw payload
 let line := HistoryKernel.pairCall ptag context rest
 let args := line ::ᵥ nil
 have hcontext : Computes p [] lineContext args context := decoder p [] ptag hp false context rest
 have hrest : Computes p [] (HistoryDecoder.decoder true) args rest := decoder p [] ptag hp true context rest
 have hraw : Computes p [] lineRaw args raw :=
  unary p [] args (HistoryDecoder.decoder false) (HistoryDecoder.decoder true) rest raw
   hrest (decoder p [] ptag hp false raw payload)
 have hline : Computes p [] lineValidator args (formulaCall vtag context raw) :=
  binary p [] args formulaValidator lineContext lineRaw context raw (formulaCall vtag context raw)
   hcontext hraw (copies p [] formulaValidator vtag hv _)
 obtain ⟨h⟩ := hline ltag hl
 exact ⟨Hilbert.Local.finish h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.LineBindingProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.LineBindingProof
