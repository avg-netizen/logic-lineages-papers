module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.RecognizesClassical
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.RecognizesExistential
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.AcceptanceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector HistoryRuleSuffix
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open OriginalQuantifierLogicalProducers
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
theorem rawAcceptanceImp {n ctx : Nat} (p : Program n) (old : Program 1)
 (isExists : Bool) (ltag ptag ctag atag fval : Nat)
 (hl : (nodes p)[ltag]? = some ⟨1,logicalLeaf old⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hf : (nodes p)[fval]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩)
 (a b : Term ctx) : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (guards isExists fval a b)
   (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall ltag (lineValue isExists ptag ctag atag a b)) (.succ .zero)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let A := guards isExists fval a b
 let G := [A]
 let av := lineValue isExists ptag ctag atag a b ::ᵥ nil
 have hguard : Hilbert.Local T ctx G A := .hypothesis List.mem_cons_self
 have hrec : Computes p G (recognizer isExists) av (.succ .zero) := by
  cases isExists with
  | false => exact RecognizesClassical.recognizes p G ptag ctag atag fval hp hc ha hf a b hguard
  | true => exact RecognizesExistential.recognizes p G ptag ctag atag fval hp hc ha hf a b hguard
 have hout : Computes p G (logicalLeaf old) av (.succ .zero) := by
  cases isExists with
  | false =>
   have hk := choosePositive p G av (recognizer false) old (constant 1 1) .zero (.succ .zero)
    hrec (constantValue p G av 1)
   exact RawCumulativeArithmetic.ArithmeticProof.chooseBoth p G
    (recognizer true) (choose (recognizer false) old (constant 1 1)) (constant 1 1) av (.succ .zero)
    hk (constantValue p G av 1)
  | true =>
   exact choosePositive p G av (recognizer true) (choose (recognizer false) old (constant 1 1))
    (constant 1 1) .zero (.succ .zero) hrec (constantValue p G av 1)
 obtain ⟨hout⟩ := hout ltag hl
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.AcceptanceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.AcceptanceProof
