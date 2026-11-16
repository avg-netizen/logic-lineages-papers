module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.RecognizesKProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.RecognizesSProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.RecognizesProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryRuleSuffix LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GuardProof
theorem recognizes {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (isS : Bool) (ptag ctag atag fval : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hf : (nodes p)[fval]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩)
 (a b c : Term ctx) (hguard : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (guards isS fval a b c)) :
 Computes p G (recognizer isS) (lineValue isS ptag ctag atag a b c ::ᵥ nil) (.succ .zero) := by
 cases isS with
 | false => exact RecognizesKProof.recognizes p G ptag ctag atag fval hp hc ha hf a b c hguard
 | true => exact RecognizesSProof.recognizes p G ptag ctag atag fval hp hc ha hf a b c hguard
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.RecognizesProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.RecognizesProof
