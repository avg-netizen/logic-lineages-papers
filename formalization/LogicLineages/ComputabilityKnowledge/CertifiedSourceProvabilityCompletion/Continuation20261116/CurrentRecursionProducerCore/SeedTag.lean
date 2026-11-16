module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TagRuntime
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.AxiomTrace
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.CallTransport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.SeedTag
open GorbowSyntax GorbowSubstitution GorbowFormulaSubstitution GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FixedFormulaSubstitution PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph
open TagPlug

theorem closedFormula {arity ctx : Nat} (p : Program arity) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (f : Formula 0) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (formulaValue ctag atag (nil : List.Vector (Term ctx) 0) f (PrescribedRuntimeSpecialization.runtimeEnvironment 0))
   (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode f))))) := by
 have he : PrescribedRuntimeSpecialization.runtimeEnvironment 0 = FullFormulaInstantiationValidity.FixedTemplateEncodingTargets.boundEnvironment 0 := by
  funext i
  exact Fin.elim0 i
 rw [he]
 exact FullFormulaInstantiationValidity.FixedTemplateEncodingStatementChecks.exactBoundFormulaEncoding 0 f arity p ctag atag hc ha ctx

theorem seed {arity ctx : Nat} (p : Program arity) (J : CurrentRecursionBaseProgram.Tags)
 (hp : (nodes p)[J.ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hm : (nodes p)[J.mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 (h13 : (nodes p)[J.r13]? = some ⟨2,UniformClosedRule13.lineConstructor⟩)
 (code : Term ctx) (tag : Nat)
 (hcode : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal code (rawNumeral (Term.numeral tag))))
 (n : Nat) (f : Formula (n+1)) (raw : List.Vector (Term ctx) n) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (CurrentRecursionBaseProgram.seedValue J n f (appendRaw raw code))
   (PrescribedSourceAxiomSpecialization.certificate J.mtag J.ctag J.atag J.r13
    (substituteFormula (CurrentRecursionBaseProgram.TagSyntax.plug n tag) f) raw))) := by
 induction n with
 | zero =>
  have hraw : raw = nil := by ext i; exact Fin.elim0 i
  subst raw
  obtain ⟨hf⟩ := TagRuntime.formula p J.ctag J.atag hc ha nil code tag hcode f
  obtain ⟨hclosed⟩ := closedFormula p J.ctag J.atag hc ha (substituteFormula (CurrentRecursionBaseProgram.TagSyntax.plug 0 tag) f)
  exact AxiomTrace.axiomCode p J hp hc _ _ (Logic.trans _ _ _ hf hclosed)
 | succ n ih =>
  let sf := substituteFormula (CurrentRecursionBaseProgram.TagSyntax.plug (n+1) tag) f
  obtain ⟨hf⟩ := TagRuntime.formula p J.ctag J.atag hc ha raw code tag hcode f
  obtain ⟨hmat⟩ := TagRuntime.headFormula p J.ctag J.atag hc ha raw.tail code tag hcode f
  obtain ⟨htail⟩ := ih (.all f) raw.tail
  obtain ⟨hline⟩ := CallTransport.rule13 p J.ctag J.r13 J.ctag J.r13 hc h13 hc h13 _ _ raw.head raw.head
   hmat (.logical (.reflexive _))
  obtain ⟨hmp⟩ := CallTransport.mp p J.mtag J.mtag hm hm _ _ _ _ _ _ hf hline htail
  simpa only [CurrentRecursionBaseProgram.seedValue,TagRuntime.rawHead,TagRuntime.rawTail,
   PrescribedSourceAxiomSpecialization.certificate,PrescribedRuntimeSpecialization.certificate,
   UniformRuntimeSpecializationStep.certificate,PrescribedRuntimeSpecialization.EnvironmentProof.stepValue,
   PrescribedRuntimeSpecialization.value,substituteFormula,CurrentRecursionBaseProgram.TagSyntax.plug,
   PrescribedSourceAxiomSpecialization.seed,GorbowStandardInduction.universalClosure]
   using (show Nonempty _ from ⟨hmp⟩)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.SeedTag
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.SeedTag
