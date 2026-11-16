module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.WrapperProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector HistoryRuleSuffix
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherPrimitivesProof LiteralRawMP.DispatcherCombinatorsProof
open SixSol20261112.Fuel NamedArithmeticGraph
theorem choosePreserves {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (test old : Program 1) (av : List.Vector (Term ctx) 1)
 (h : Computes p G old av (.succ .zero)) :
 Computes p G (choose test old (constant 1 1)) av (.succ .zero) :=
 RawCumulativeArithmetic.ArithmeticProof.chooseBoth p G test old (constant 1 1) av (.succ .zero)
  h (constantValue p G av 1)

theorem cumulative {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (f : Formula 1) (lhs rhs : Term 1) (old : Program 1) (av : List.Vector (Term ctx) 1)
 (h : Computes p G old av (.succ .zero)) :
 Computes p G (CumulativePropositionalSource.logical f lhs rhs old) av (.succ .zero) := by
 repeat first | exact h | apply choosePreserves

theorem inner {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (rawOld : Program 1)
 (isExists : Bool) (ptag ctag atag fval : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hf : (nodes p)[fval]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩)
 (a b : Term ctx)
 (hguard : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (OriginalQuantifierLogicalExtension.guards isExists fval a b)) :
 Computes p G (CurrentQuantifierLogicalSource.selectedOld rawOld)
  (OriginalQuantifierLogicalProducers.lineValue isExists ptag ctag atag a b ::ᵥ nil) (.succ .zero) := by
 let av := OriginalQuantifierLogicalProducers.lineValue isExists ptag ctag atag a b ::ᵥ nil
 have hrec : Computes p G (OriginalQuantifierLogicalExtension.recognizer isExists) av (.succ .zero) := by
  cases isExists with
  | false => exact OriginalQuantifierLogicalExtension.RecognizesClassical.recognizes p G ptag ctag atag fval hp hc ha hf a b hguard
  | true => exact OriginalQuantifierLogicalExtension.RecognizesExistential.recognizes p G ptag ctag atag fval hp hc ha hf a b hguard
 cases isExists with
 | false =>
  apply choosePreserves
  exact choosePositive p G av _ _ _ .zero (.succ .zero) hrec (constantValue p G av 1)
 | true =>
  exact choosePositive p G av _ _ _ .zero (.succ .zero) hrec (constantValue p G av 1)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.WrapperProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.WrapperProof
