module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.InternalAtomsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open LiteralSyntaxStep.StepSupportProof
theorem secondComputed {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (htag ttag : Nat)
 (hh : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩)
 (ht : (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩) (args : Term ctx) :
 Computes p G secondArg (args ::ᵥ nil) (secondValue htag ttag args) :=
 unary p G (args ::ᵥ nil) HistoryLookup.head HistoryLookup.tail _ _
  (copies p G HistoryLookup.tail ttag ht _) (copies p G HistoryLookup.head htag hh _)
theorem thirdComputed {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (htag ttag : Nat)
 (hh : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩)
 (ht : (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩) (args : Term ctx) :
 Computes p G thirdArg (args ::ᵥ nil) (thirdValue htag ttag args) :=
 unary p G (args ::ᵥ nil) HistoryLookup.head (applyOne HistoryLookup.tail HistoryLookup.tail) _ _
  (unary p G (args ::ᵥ nil) HistoryLookup.tail HistoryLookup.tail _ _
   (copies p G HistoryLookup.tail ttag ht _) (copies p G HistoryLookup.tail ttag ht _))
  (copies p G HistoryLookup.head htag hh _)
theorem leftComputed {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (itag htag ttag : Nat)
 (hi : (nodes p)[itag]? = some ⟨2,UniformClosedInstanceRecognizer.instanceCode⟩)
 (hh : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩)
 (ht : (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩) (args : Term ctx) :
 Computes p G leftInstance (args ::ᵥ nil) (leftValue itag htag ttag args) :=
 binary p G (args ::ᵥ nil) UniformClosedInstanceRecognizer.instanceCode firstArg secondArg _ _ _
  (copies p G HistoryLookup.head htag hh _) (secondComputed p G htag ttag hh ht args)
  (copies p G UniformClosedInstanceRecognizer.instanceCode itag hi _)
theorem rightComputed {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (itag htag ttag : Nat)
 (hi : (nodes p)[itag]? = some ⟨2,UniformClosedInstanceRecognizer.instanceCode⟩)
 (hh : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩)
 (ht : (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩) (args : Term ctx) :
 Computes p G rightInstance (args ::ᵥ nil) (rightValue itag htag ttag args) :=
 binary p G (args ::ᵥ nil) UniformClosedInstanceRecognizer.instanceCode firstArg thirdArg _ _ _
  (copies p G HistoryLookup.head htag hh _) (thirdComputed p G htag ttag hh ht args)
  (copies p G UniformClosedInstanceRecognizer.instanceCode itag hi _)
theorem implicationComputed {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (itag htag ttag ctag atag : Nat)
 (hi : (nodes p)[itag]? = some ⟨2,UniformClosedInstanceRecognizer.instanceCode⟩)
 (hh : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩)
 (ht : (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) (args left right : Term ctx)
 (hleft : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (leftValue itag htag ttag args) (.succ left)))
 (hright : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (rightValue itag htag ttag args) (.succ right))) :
 Computes p G implication (args ::ᵥ nil)
  (formulaValue ctag atag (secondValue htag ttag args) (thirdValue htag ttag args) left right) := by
 let av := args ::ᵥ nil
 have hl := changeValue p G leftInstance av _ (.succ left) (leftComputed p G itag htag ttag hi hh ht args) hleft
 have hr := changeValue p G rightInstance av _ (.succ right) (rightComputed p G itag htag ttag hi hh ht args) hright
 have hleftResult : Computes p G leftResult av left :=
  unary p G av HistoryCodec.predecessor leftInstance (.succ left) left hl (predecessor p G left)
 have hrightResult : Computes p G rightResult av right :=
  unary p G av HistoryCodec.predecessor rightInstance (.succ right) right hr (predecessor p G right)
 have heq : Computes p G equality av
  (FixedFormulaSubstitution.binaryValue ctag atag 0 (secondValue htag ttag args) (thirdValue htag ttag args)) :=
  binary p G av HistoryCodec.cons _ _ _ _ _ (constantValue p G av 0)
   (binary p G av HistoryAppend.append secondArg thirdArg _ _ _
    (secondComputed p G htag ttag hh ht args) (thirdComputed p G htag ttag hh ht args)
    (copies p G HistoryAppend.append atag ha _)) (copies p G HistoryCodec.cons ctag hc _)
 have hcon : Computes p G consequent av (FixedFormulaSubstitution.binaryValue ctag atag 7 left right) :=
  binary p G av HistoryCodec.cons _ _ _ _ _ (constantValue p G av 7)
   (binary p G av HistoryAppend.append leftResult rightResult left right _ hleftResult hrightResult
    (copies p G HistoryAppend.append atag ha _)) (copies p G HistoryCodec.cons ctag hc _)
 exact binary p G av HistoryCodec.cons _ _ _ _ _ (constantValue p G av 7)
  (binary p G av HistoryAppend.append equality consequent _ _ _ heq hcon
   (copies p G HistoryAppend.append atag ha _)) (copies p G HistoryCodec.cons ctag hc _)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.InternalAtomsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.InternalAtomsProof
