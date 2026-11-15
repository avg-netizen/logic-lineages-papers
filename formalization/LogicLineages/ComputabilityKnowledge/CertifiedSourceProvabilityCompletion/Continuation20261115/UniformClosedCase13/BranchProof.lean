module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.InternalAtomsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.BranchProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open LiteralSyntaxStep.StepSupportProof RelationalSyntaxDepthTransport.ExpansionCasesSupportProof InternalAtomsProof
theorem lengthTrue {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ltag : Nat)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩) (args : Term ctx)
 (hL : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (HistoryLengthOffset.lengthCall ltag args) (Term.numeral 2))) :
 Computes p G (applyTwo equalCode HistoryLengthOffset.lengthProgram (constant 1 2)) (args ::ᵥ nil) (.succ .zero) := by
 apply binary p G (args ::ᵥ nil) equalCode _ _ _ _ _ (copies p G _ ltag hl _) (constantValue p G _ 2)
 intro tag ht
 obtain ⟨he⟩ := HistoryKernel.EqualProof.internalEqualComplete n p tag ht ctx (HistoryLengthOffset.lengthCall ltag args) (Term.numeral 2)
 exact ⟨.mp (.base he) hL⟩
theorem lengthFalse {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ltag : Nat)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩) (args : Term ctx)
 (hL : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.neg (.equal (HistoryLengthOffset.lengthCall ltag args) (Term.numeral 2)))) :
 Computes p G (applyTwo equalCode HistoryLengthOffset.lengthProgram (constant 1 2)) (args ::ᵥ nil) .zero :=
 binary p G (args ::ᵥ nil) equalCode _ _ _ _ _ (copies p G _ ltag hl _) (constantValue p G _ 2)
  (equalFalseLocal p G (HistoryLengthOffset.lengthCall ltag args) (Term.numeral 2) hL)
theorem accepted {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (itag ltag htag ttag ctag atag : Nat)
 (hi : (nodes p)[itag]? = some ⟨2,UniformClosedInstanceRecognizer.instanceCode⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hh : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩)
 (ht : (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) (args result : Term ctx)
 (hL : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (HistoryLengthOffset.lengthCall ltag args) (Term.numeral 2)))
 (hI : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (instanceValue itag htag ttag args) (.succ result))) :
 Computes p G caseCode (args ::ᵥ nil) (.succ (formulaValue ctag atag (firstValue htag args) result)) := by
 have hins := changeValue p G instantiated (args ::ᵥ nil) _ (.succ result)
  (instantiatedValue p G itag htag ttag hi hh ht args) hI
 have hout := implicationValue p G itag htag ttag ctag atag hi hh ht hc ha args result hI
 have hsome := unary p G (args ::ᵥ nil) .succ implication _ _ hout
  (UniformClosedInstanceRecognizer.InternalOutputProof.succComputes p G _)
 exact choosePositive p G (args ::ᵥ nil) _ _ _ .zero _ (lengthTrue p G ltag hl args hL)
  (choosePositive p G (args ::ᵥ nil) _ _ _ result _ hins hsome)
theorem rejectLength {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ltag : Nat)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩) (args : Term ctx)
 (hL : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.neg (.equal (HistoryLengthOffset.lengthCall ltag args) (Term.numeral 2)))) :
 Computes p G caseCode (args ::ᵥ nil) .zero :=
 chooseZero p G (args ::ᵥ nil) _ _ _ .zero (lengthFalse p G ltag hl args hL) (constantValue p G _ 0)
theorem rejectNone {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (itag ltag htag ttag : Nat)
 (hi : (nodes p)[itag]? = some ⟨2,UniformClosedInstanceRecognizer.instanceCode⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hh : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩)
 (ht : (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩) (args : Term ctx)
 (hL : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (HistoryLengthOffset.lengthCall ltag args) (Term.numeral 2)))
 (hI : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (instanceValue itag htag ttag args) .zero)) :
 Computes p G caseCode (args ::ᵥ nil) .zero := by
 have hins := changeValue p G instantiated (args ::ᵥ nil) _ .zero
  (instantiatedValue p G itag htag ttag hi hh ht args) hI
 exact choosePositive p G (args ::ᵥ nil) _ _ _ .zero .zero (lengthTrue p G ltag hl args hL)
  (chooseZero p G (args ::ᵥ nil) _ _ _ .zero hins (constantValue p G _ 0))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.BranchProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.BranchProof
