module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.InternalAtomsProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeArithmetic.ArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.BranchProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open LiteralSyntaxStep.StepSupportProof RelationalSyntaxDepthTransport.ExpansionCasesSupportProof InternalAtomsProof
open Continuation20261114.RawCumulativeArithmetic.ArithmeticProof
theorem lengthTrue {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ltag : Nat)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩) (args : Term ctx)
 (hL : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (HistoryLengthOffset.lengthCall ltag args) (Term.numeral 3))) :
 Computes p G (applyTwo equalCode HistoryLengthOffset.lengthProgram (constant 1 3)) (args ::ᵥ nil) (.succ .zero) := by
 apply binary p G (args ::ᵥ nil) equalCode _ _ _ _ _ (copies p G _ ltag hl _) (constantValue p G _ 3)
 intro tag ht
 obtain ⟨he⟩ := HistoryKernel.EqualProof.internalEqualComplete n p tag ht ctx (HistoryLengthOffset.lengthCall ltag args) (Term.numeral 3)
 exact ⟨.mp (.base he) hL⟩
theorem lengthFalse {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ltag : Nat)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩) (args : Term ctx)
 (hL : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.neg (.equal (HistoryLengthOffset.lengthCall ltag args) (Term.numeral 3)))) :
 Computes p G (applyTwo equalCode HistoryLengthOffset.lengthProgram (constant 1 3)) (args ::ᵥ nil) .zero :=
 binary p G (args ::ᵥ nil) equalCode _ _ _ _ _ (copies p G _ ltag hl _) (constantValue p G _ 3)
  (equalFalseLocal p G (HistoryLengthOffset.lengthCall ltag args) (Term.numeral 3) hL)
theorem accepted {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (itag ltag htag ttag ctag atag : Nat)
 (hi : (nodes p)[itag]? = some ⟨2,UniformClosedInstanceRecognizer.instanceCode⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hh : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩)
 (ht : (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) (args left right : Term ctx)
 (hL : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (HistoryLengthOffset.lengthCall ltag args) (Term.numeral 3)))
 (hleft : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (leftValue itag htag ttag args) (.succ left)))
 (hright : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (rightValue itag htag ttag args) (.succ right))) :
 Computes p G caseCode (args ::ᵥ nil)
  (.succ (formulaValue ctag atag (secondValue htag ttag args) (thirdValue htag ttag args) left right)) := by
 have hleftCall := changeValue p G leftInstance (args ::ᵥ nil) _ (.succ left)
  (leftComputed p G itag htag ttag hi hh ht args) hleft
 have hrightCall := changeValue p G rightInstance (args ::ᵥ nil) _ (.succ right)
  (rightComputed p G itag htag ttag hi hh ht args) hright
 have hout := implicationComputed p G itag htag ttag ctag atag hi hh ht hc ha args left right hleft hright
 have hsome := unary p G (args ::ᵥ nil) .succ implication _ _ hout
  (UniformClosedInstanceRecognizer.InternalOutputProof.succComputes p G _)
 exact choosePositive p G (args ::ᵥ nil) _ _ _ .zero _ (lengthTrue p G ltag hl args hL)
  (choosePositive p G (args ::ᵥ nil) _ _ _ left _ hleftCall
   (choosePositive p G (args ::ᵥ nil) _ _ _ right _ hrightCall hsome))
theorem rejectLength {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ltag : Nat)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩) (args : Term ctx)
 (hL : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.neg (.equal (HistoryLengthOffset.lengthCall ltag args) (Term.numeral 3)))) :
 Computes p G caseCode (args ::ᵥ nil) .zero :=
 chooseZero p G (args ::ᵥ nil) _ _ _ .zero (lengthFalse p G ltag hl args hL) (constantValue p G _ 0)
theorem rejectLeft {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (itag htag ttag : Nat)
 (hi : (nodes p)[itag]? = some ⟨2,UniformClosedInstanceRecognizer.instanceCode⟩)
 (hh : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩)
 (ht : (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩) (args : Term ctx)
 (hI : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (leftValue itag htag ttag args) .zero)) :
 Computes p G caseCode (args ::ᵥ nil) .zero := by
 have hins := changeValue p G leftInstance (args ::ᵥ nil) _ .zero
  (leftComputed p G itag htag ttag hi hh ht args) hI
 have hinner := chooseZero p G (args ::ᵥ nil) leftInstance (constant 1 0)
  (choose rightInstance (constant 1 0) (applyOne .succ implication)) .zero hins (constantValue p G _ 0)
 exact chooseBoth p G _ (constant 1 0) _ (args ::ᵥ nil) .zero (constantValue p G _ 0) hinner
theorem rejectRight {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (itag htag ttag : Nat)
 (hi : (nodes p)[itag]? = some ⟨2,UniformClosedInstanceRecognizer.instanceCode⟩)
 (hh : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩)
 (ht : (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩) (args : Term ctx)
 (hI : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (rightValue itag htag ttag args) .zero)) :
 Computes p G caseCode (args ::ᵥ nil) .zero := by
 have hins := changeValue p G rightInstance (args ::ᵥ nil) _ .zero
  (rightComputed p G itag htag ttag hi hh ht args) hI
 have hright := chooseZero p G (args ::ᵥ nil) rightInstance (constant 1 0)
  (applyOne .succ implication) .zero hins (constantValue p G _ 0)
 have hinner := chooseBoth p G leftInstance (constant 1 0)
  (choose rightInstance (constant 1 0) (applyOne .succ implication))
  (args ::ᵥ nil) .zero (constantValue p G _ 0) hright
 exact chooseBoth p G _ (constant 1 0) _ (args ::ᵥ nil) .zero (constantValue p G _ 0) hinner
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.BranchProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.BranchProof
