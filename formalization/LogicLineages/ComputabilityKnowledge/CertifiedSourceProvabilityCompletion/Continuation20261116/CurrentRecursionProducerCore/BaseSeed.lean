module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.SeedTag
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.SpecializationCopy
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.BaseSeed
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FixedFormulaSubstitution GorbowFormulaSubstitution PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph

theorem certificate {arity ctx m : Nat} (p : Program arity) (J K : CurrentRecursionBaseProgram.Tags)
 (hp : (nodes p)[J.ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hm : (nodes p)[J.mtag]? = some ⟨4,LiteralRawMP.constructor⟩) (hr : (nodes p)[J.r13]? = some ⟨2,UniformClosedRule13.lineConstructor⟩)
 (hn : (nodes p)[J.ntag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (kc : (nodes p)[K.ctag]? = some ⟨2,HistoryCodec.cons⟩) (ka : (nodes p)[K.atag]? = some ⟨2,HistoryAppend.append⟩)
 (km : (nodes p)[K.mtag]? = some ⟨4,LiteralRawMP.constructor⟩) (kr : (nodes p)[K.r13]? = some ⟨2,UniformClosedRule13.lineConstructor⟩)
 (target : Nat) (inputs other : List.Vector (Term ctx) m)
 (hraw : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralNumeralPrefix.numeralCall J.ntag (inputs.get i)) (other.get i))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (CurrentRecursionBaseProgram.seedValue J m (CurrentRecursionBaseProgram.rootTemplate m)
    (CurrentRecursionBaseProgram.rawValues J (Term.numeral target) inputs))
   (PrescribedSourceAxiomSpecialization.certificate K.mtag K.ctag K.atag K.r13
    (CurrentRecursionBaseCertificate.rootFormula m target) other))) := by
 let C := CurrentCalculationFormulaProgram.codecTags J.ctag J.atag J.ntag
 obtain ⟨htag⟩ := ValueTraceProof.numeral (ctx := ctx) p C hn target
 obtain ⟨hseed⟩ := SeedTag.seed p J hp hc ha hm hr _ target htag m (CurrentRecursionBaseProgram.rootTemplate m)
  (inputs.map (LiteralNumeralPrefix.numeralCall J.ntag))
 rw [TagRuntime.rawValues,CurrentRecursionBaseProgram.TagSyntax.root] at hseed
 have hargs : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal ((inputs.map (LiteralNumeralPrefix.numeralCall J.ntag)).get i) (other.get i)) := by
  intro i
  simpa only [List.Vector.get_map] using hraw i
 obtain ⟨hcopy⟩ := SpecializationCopy.certificate p J K hc ha hm hr kc ka km kr m
  (CurrentRecursionBaseCertificate.rootFormula m target) _ other hargs _ _ (.logical (.reflexive _))
 exact ⟨Logic.trans _ _ _ hseed hcopy⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.BaseSeed
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.BaseSeed
