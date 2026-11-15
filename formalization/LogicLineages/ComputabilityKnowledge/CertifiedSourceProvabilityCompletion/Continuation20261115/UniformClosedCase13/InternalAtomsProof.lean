module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.InternalAtomsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open LiteralSyntaxStep.StepSupportProof
/-- Runtime argument list remains arbitrary. Actual head/tail calls are copied
inside the same registry; no pair-shaped annotation is assumed. -/
theorem instantiatedValue {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (itag htag ttag : Nat)
 (hi : (nodes p)[itag]? = some ⟨2,UniformClosedInstanceRecognizer.instanceCode⟩)
 (hh : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩)
 (ht : (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩) (args : Term ctx) :
 Computes p G instantiated (args ::ᵥ nil) (instanceValue itag htag ttag args) := by
 exact binary p G (args ::ᵥ nil) UniformClosedInstanceRecognizer.instanceCode firstArg secondArg _ _ _
  (copies p G HistoryLookup.head htag hh _)
  (unary p G (args ::ᵥ nil) HistoryLookup.head HistoryLookup.tail _ _
   (copies p G HistoryLookup.tail ttag ht _) (copies p G HistoryLookup.head htag hh _))
  (copies p G UniformClosedInstanceRecognizer.instanceCode itag hi _)
/-- Actual Some predecessor and literal unary10/binary7 construction. -/
theorem implicationValue {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (itag htag ttag ctag atag : Nat)
 (hi : (nodes p)[itag]? = some ⟨2,UniformClosedInstanceRecognizer.instanceCode⟩)
 (hh : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩)
 (ht : (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) (args result : Term ctx)
 (hI : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (instanceValue itag htag ttag args) (.succ result))) :
 Computes p G implication (args ::ᵥ nil) (formulaValue ctag atag (firstValue htag args) result) := by
 let av := args ::ᵥ nil
 have hins := changeValue p G instantiated av _ (.succ result) (instantiatedValue p G itag htag ttag hi hh ht args) hI
 have hresult : Computes p G instanceResult av result :=
  unary p G av HistoryCodec.predecessor instantiated (.succ result) result hins (predecessor p G result)
 have hquant : Computes p G quantified av (HistoryLookup.consCall ctag (Term.numeral 10) (firstValue htag args)) :=
  binary p G av HistoryCodec.cons _ _ _ _ _ (constantValue p G av 10)
   (copies p G HistoryLookup.head htag hh _) (copies p G HistoryCodec.cons ctag hc _)
 exact binary p G av HistoryCodec.cons _ _ _ _ _ (constantValue p G av 7)
  (binary p G av HistoryAppend.append quantified instanceResult _ result _ hquant hresult
   (copies p G HistoryAppend.append atag ha _))
  (copies p G HistoryCodec.cons ctag hc _)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.InternalAtomsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.InternalAtomsProof
