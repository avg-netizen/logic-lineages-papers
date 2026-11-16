module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.SeedCopy
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph
open CurrentRecursionProducerCore
theorem certificate {arity ctx m n : Nat} (p : Program arity) (J K : CurrentRecursionBaseProgram.Tags)
 (hp : (nodes p)[J.ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hm : (nodes p)[J.mtag]? = some ⟨4,LiteralRawMP.constructor⟩) (hr : (nodes p)[J.r13]? = some ⟨2,UniformClosedRule13.lineConstructor⟩)
 (hn : (nodes p)[J.ntag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (kc : (nodes p)[K.ctag]? = some ⟨2,HistoryCodec.cons⟩) (ka : (nodes p)[K.atag]? = some ⟨2,HistoryAppend.append⟩)
 (km : (nodes p)[K.mtag]? = some ⟨4,LiteralRawMP.constructor⟩) (kr : (nodes p)[K.r13]? = some ⟨2,UniformClosedRule13.lineConstructor⟩)
 (f : Program n) (g : Fin n → Program m) (target : Nat) (inputs other : List.Vector (Term ctx) m)
 (hraw : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralNumeralPrefix.numeralCall J.ntag (inputs.get i)) (other.get i))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (CurrentRecursionBaseProgram.seedValue J m (CurrentCompositionProducerProgram.rootTemplate f g)
    (CurrentRecursionBaseProgram.rawValues J (Term.numeral target) inputs))
   (PrescribedSourceAxiomSpecialization.certificate K.mtag K.ctag K.atag K.r13
    (CurrentCompositionCertificate.rootFormula f g target) other))) := by
 let C := CurrentCalculationFormulaProgram.codecTags J.ctag J.atag J.ntag
 obtain ⟨htag⟩ := ValueTraceProof.numeral (ctx := ctx) p C hn target
 dsimp only [C,CurrentCalculationFormulaProgram.codecTags] at htag
 obtain ⟨hseed⟩ := SeedTag.seed p J hp hc ha hm hr _ target htag m (CurrentCompositionProducerProgram.rootTemplate f g)
  (inputs.map (LiteralNumeralPrefix.numeralCall J.ntag))
 rw [TagRuntime.rawValues,CurrentCompositionProducerProgram.SyntaxProof.root] at hseed
 have hargs : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal ((inputs.map (LiteralNumeralPrefix.numeralCall J.ntag)).get i) (other.get i)) := by
  intro i
  simpa only [List.Vector.get_map] using hraw i
 obtain ⟨hcopy⟩ := SpecializationCopy.certificate p J K hc ha hm hr kc ka km kr m
  (CurrentCompositionCertificate.rootFormula f g target) _ other hargs _ _ (.logical (.reflexive _))
 exact ⟨Logic.trans _ _ _ hseed hcopy⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.SeedCopy
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.SeedCopy
