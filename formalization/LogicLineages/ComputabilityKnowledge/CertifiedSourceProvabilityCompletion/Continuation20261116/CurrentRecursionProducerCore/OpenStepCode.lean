module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.SeedTag
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.SpecializationCopy
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.OpenStepCode
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FixedFormulaSubstitution GorbowFormulaSubstitution PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph

theorem term {arity ctx m : Nat} (p : Program arity) (J : CurrentRecursionBaseProgram.Tags)
 (c a : Nat)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hn : (nodes p)[J.ntag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (kc : (nodes p)[c]? = some ⟨2,HistoryCodec.cons⟩) (ka : (nodes p)[a]? = some ⟨2,HistoryAppend.append⟩)
 (offset target : Nat) (inputs other : List.Vector (Term ctx) (m+1))
 (hraw : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralNumeralPrefix.numeralCall J.ntag (inputs.get i)) (other.get i))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag (PrescribedRuntimeSpecialization.headEnvironment (m+2))
    (CurrentRecursionBaseProgram.rawValues J (Term.numeral target) inputs)
    (CurrentRecursionStepProgram.unaryTemplate m offset))
   (termValue c a (CurrentRecursionStepCertificate.stepEnvironment m) other
    (CurrentRecursionStepCertificate.stepTemplate m (target+offset))))) := by
 let C := CurrentCalculationFormulaProgram.codecTags J.ctag J.atag J.ntag
 obtain ⟨htag⟩ := ValueTraceProof.numeral (ctx := ctx) p C hn target
 dsimp only [C,CurrentCalculationFormulaProgram.codecTags] at htag
 have hplug := TagPlug.termPlug p J.ctag J.atag hc ha (PrescribedRuntimeSpecialization.headEnvironment (m+1))
  (inputs.map (LiteralNumeralPrefix.numeralCall J.ntag)) _ target htag
  (CurrentRecursionStepProgram.unaryTemplate m offset)
 rw [TagRuntime.head,TagRuntime.rawValues,CurrentRecursionStepProgram.RuntimeSyntax.unaryPlug] at hplug
 obtain ⟨hplug⟩ := hplug
 obtain ⟨hcopy⟩ := CurrentCompositionCertificate.TermCopiesProof.term p J.ctag J.atag c a hc ha kc ka
  (PrescribedRuntimeSpecialization.headEnvironment (m+1)) (inputs.map (LiteralNumeralPrefix.numeralCall J.ntag))
  (CurrentRecursionStepCertificate.stepTemplate m (target+offset))
 have hargs : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal ((inputs.map (LiteralNumeralPrefix.numeralCall J.ntag)).get i) (other.get i)) := by
  intro i
  simpa only [List.Vector.get_map] using hraw i
 obtain ⟨hother⟩ := FormulaRaw.term p c a kc ka _ other hargs
  (PrescribedRuntimeSpecialization.headEnvironment (m+1)) (CurrentRecursionStepCertificate.stepTemplate m (target+offset))
 exact ⟨Logic.trans _ _ _ hplug (Logic.trans _ _ _ hcopy hother)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.OpenStepCode
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.OpenStepCode
