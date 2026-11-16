module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.RecognizesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.AcceptanceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryRuleSuffix LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open RecognizesProof
theorem rawAcceptanceImp {n ctx : Nat} (p : Program n) (old : Program 1)
 (isS : Bool) (ltag ptag ctag atag fval : Nat)
 (hl : (nodes p)[ltag]? = some ⟨1,logicalLeaf old⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hf : (nodes p)[fval]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩)
 (a b c : Term ctx) : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (guards isS fval a b c)
   (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall ltag (lineValue isS ptag ctag atag a b c)) (.succ .zero)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let A := guards isS fval a b c
 let G := [A]
 let av := lineValue isS ptag ctag atag a b c ::ᵥ nil
 have hguard : Hilbert.Local T ctx G A := .hypothesis List.mem_cons_self
 have hrec := recognizes p G isS ptag ctag atag fval hp hc ha hf a b c hguard
 have hout : Computes p G (logicalLeaf old) av (.succ .zero) := by
  cases isS with
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
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.AcceptanceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.AcceptanceProof
