module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer.InternalOutputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer.BranchProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open RelationalSyntaxDepthTransport.ExpansionCasesSupportProof InternalOutputProof
theorem testTrue {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (args : List.Vector (Term ctx) 2) (code : Program 2) (value : Term ctx)
 (hv : Computes p G code args value)
 (h : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (.equal value (.succ .zero))) :
 Computes p G (applyTwo equalCode code (constant 2 1)) args (.succ .zero) := by
 apply binary p G args equalCode code (constant 2 1) value (.succ .zero) (.succ .zero) hv (constantValue p G args 1)
 intro tag ht
 obtain ⟨he⟩ := HistoryKernel.EqualProof.internalEqualComplete n p tag ht ctx value (.succ .zero)
 exact ⟨.mp (.base he) h⟩
theorem testFalse {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (args : List.Vector (Term ctx) 2) (code : Program 2) (value : Term ctx)
 (hv : Computes p G code args value)
 (h : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (.neg (.equal value (.succ .zero)))) :
 Computes p G (applyTwo equalCode code (constant 2 1)) args .zero :=
 binary p G args equalCode code (constant 2 1) value (.succ .zero) .zero hv (constantValue p G args 1)
  (equalFalseLocal p G value (.succ .zero) h)

theorem accepted {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ftag fval vtag ptag ctag rtag : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (hfv : (nodes p)[fval]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩)
 (hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩) (formula replacement : Term ctx)
 (hF : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxValidator.formulaCall fval (.succ .zero) formula) (.succ .zero)))
 (hV : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (Continuation20261114.RawReflexivityDispatcher.valid vtag replacement)) :
 Computes p G instanceCode (formula ::ᵥ replacement ::ᵥ nil)
  (.succ (outputValue ftag ptag ctag rtag formula replacement)) := by
 let args := formula ::ᵥ replacement ::ᵥ nil
 have htF := testTrue p G args formulaGuard _ (formulaValue p G fval hfv formula replacement) hF
 have htV := testTrue p G args termGuard _ (termValue p G vtag hv formula replacement) hV
 have hout := output p G ftag ptag ctag rtag hf hp hc hr formula replacement
 have hsome := unary p G args .succ outputCode _ _ hout (succComputes p G _)
 exact choosePositive p G args _ _ _ .zero _ htF
  (choosePositive p G args _ _ _ .zero _ htV hsome)

theorem rejectFormula {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (fval : Nat)
 (hfv : (nodes p)[fval]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩) (formula replacement : Term ctx)
 (hF : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.neg (.equal (LiteralSyntaxValidator.formulaCall fval (.succ .zero) formula) (.succ .zero)))) :
 Computes p G instanceCode (formula ::ᵥ replacement ::ᵥ nil) .zero := by
 let args := formula ::ᵥ replacement ::ᵥ nil
 exact chooseZero p G args _ _ _ .zero
  (testFalse p G args formulaGuard _ (formulaValue p G fval hfv formula replacement) hF)
  (constantValue p G args 0)

theorem rejectTerm {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (fval vtag : Nat)
 (hfv : (nodes p)[fval]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩)
 (hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩) (formula replacement : Term ctx)
 (hF : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxValidator.formulaCall fval (.succ .zero) formula) (.succ .zero)))
 (hV : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.neg (Continuation20261114.RawReflexivityDispatcher.valid vtag replacement))) :
 Computes p G instanceCode (formula ::ᵥ replacement ::ᵥ nil) .zero := by
 let args := formula ::ᵥ replacement ::ᵥ nil
 exact choosePositive p G args _ _ _ .zero .zero
  (testTrue p G args formulaGuard _ (formulaValue p G fval hfv formula replacement) hF)
  (chooseZero p G args _ _ _ .zero
   (testFalse p G args termGuard _ (termValue p G vtag hv formula replacement) hV)
   (constantValue p G args 0))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer.BranchProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer.BranchProof
