module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.OperandBridge
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.SeedCopy
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.CodeBridge
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph
open CurrentRecursionProducerCore

theorem value {arity k m n ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX))
 (f : Program n) (g : Fin n → Program m) (F : Program (n+1)) (G : Fin n → Program (m+1))
 (J : CurrentCompositionProducerProgram.Tags n) (H : CurrentCompositionProducerProgram.Installation p f g F G J)
 (target : Nat) (ht : (nodes p)[target]? = some ⟨m,Program.composition f g⟩) (inputs : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (CurrentCompositionProducerProgram.value f g J (Term.numeral target) inputs)
   (CurrentCompositionCertificate.certificate I.previous f g target inputs (childValues f g target inputs)
    (call (target+1) (childValues f g target inputs))
    (List.Vector.ofFn (fun i => producerCode (J.argumentProducerTags i) (target+argumentTag f g i) inputs))
    (producerCode J.functionProducerTag (target+1) (childValues f g target inputs))))) := by
 let K := tags I.previous
 have L := OriginalProof.installed p installed lhs rhs t old a _ I
 have hJ := TupleCopy.nodes p J.C H.primitives
 have hK := TupleCopy.nodes p K L
 let values := childValues f g target inputs
 let actualValues := List.Vector.ofFn (fun i => call (J.argumentTags i) inputs)
 let nums := inputs.map (LiteralNumeralPrefix.numeralCall J.C.numeralTag)
 let nums' := inputs.map (LiteralNumeralPrefix.numeralCall K.numeralTag)
 let leftArgs := List.Vector.ofFn (fun i => callValue J.C (CurrentRecursionStepProgram.shiftTerm (argumentTag f g i) (Term.numeral target)) nums)
 let leftArgs' := CurrentCompositionCertificate.childValues K f g target nums'
 let rightArgs := actualValues.map (LiteralNumeralPrefix.numeralCall J.C.numeralTag)
 let rightArgs' := values.map (LiteralNumeralPrefix.numeralCall K.numeralTag)
 let codes := List.Vector.ofFn (fun i => call (J.argumentProducerTags i)
  (CurrentRecursionStepProgram.shiftTerm (argumentTag f g i) (Term.numeral target) ::ᵥ inputs))
 let codes' := List.Vector.ofFn (fun i => producerCode (J.argumentProducerTags i) (target+argumentTag f g i) inputs)
 have hlefts : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (leftArgs.get i) (leftArgs'.get i))) := by
  intro i
  simp only [leftArgs,leftArgs',CurrentCompositionCertificate.childValues,List.Vector.get_ofFn]
  exact OperandBridge.leftArgument p f g J.C K H.primitives L target inputs i
 have hrights : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (rightArgs.get i) (rightArgs'.get i))) := by
  intro i
  simp only [rightArgs,rightArgs',List.Vector.get_map,actualValues,List.Vector.get_ofFn]
  exact OperandBridge.rightArgument p f g F G J H K L target ht inputs i
 obtain ⟨hlefts⟩ := SpecializationCopy.finiteWitness n _ hlefts
 obtain ⟨hrights⟩ := SpecializationCopy.finiteWitness n _ hrights
 have hcodes : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (codes.get i) (codes'.get i)) := by
  intro i
  simp only [codes,codes',List.Vector.get_ofFn,producerCode,CurrentRecursionProducerCore.childCode,
   CurrentRecursionStepProgram.TemplateSyntax.shiftNumeral]
  exact .logical (.reflexive _)
 obtain ⟨hparent⟩ := CodecBridge.call p J.C K hJ hK (Term.numeral target) inputs
 obtain ⟨hleft⟩ := CallRawCopy.call p J.C K hJ hK (Term.numeral (target+1)) leftArgs leftArgs' hlefts
 obtain ⟨hright⟩ := CallRawCopy.call p J.C K hJ hK (Term.numeral (target+1)) rightArgs rightArgs' hrights
 obtain ⟨houtput⟩ := OperandBridge.output p f g F G J H K L target ht inputs
 obtain ⟨hcongr⟩ := CallCopy.certificate p J.C K H.primitives L (Term.numeral (target+1))
  leftArgs rightArgs codes leftArgs' rightArgs' codes' hlefts hrights hcodes
 obtain ⟨hfunction⟩ := EvaluationBridge.functionCode p f g F G J H target ht inputs
 let S : CurrentRecursionBaseProgram.Tags :=
  ⟨J.ptag,I.previous.previous.current.ctag,I.previous.previous.current.atag,K.numeralTag,K.mtag,K.constructorTag,
   I.previous.previous.current.constructorTag,J.functionTag,J.functionProducerTag⟩
 have hraw : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralNumeralPrefix.numeralCall J.C.numeralTag (inputs.get i)) (nums'.get i))) := by
  intro i
  simp only [nums',List.Vector.get_map]
  exact CodecBridge.numeral p J.C K hJ hK (inputs.get i)
 obtain ⟨hraw⟩ := SpecializationCopy.finiteWitness m _ hraw
 obtain ⟨hseed⟩ := SeedCopy.certificate p (CurrentCompositionProducerProgram.seedTags J) S H.hp H.primitives.hc H.primitives.ha
  H.primitives.hm H.h13 H.primitives.hn I.previous.previous.current.h_ctag I.previous.previous.current.h_atag L.hm
  I.previous.previous.current.h_constructor f g target inputs nums' hraw
 obtain ⟨hfirst⟩ := TransitivityCopy.certificate p J.C.mtag J.C.ctag J.C.atag J.C.constructorTag K.mtag K.ctag K.atag K.constructorTag
  H.primitives.hm H.primitives.hc H.primitives.ha H.primitives.h12 L.hm L.hc L.ha L.h12 _ _ _ _ _ _ _ _ _ _ hparent hleft hright hseed hcongr
 have hout := TransitivityCopy.certificate p J.C.mtag J.C.ctag J.C.atag J.C.constructorTag K.mtag K.ctag K.atag K.constructorTag
  H.primitives.hm H.primitives.hc H.primitives.ha H.primitives.h12 L.hm L.hc L.ha L.h12 _ _ _ _ _ _ _ _ _ _ hparent hright houtput hfirst hfunction
 simp only [CurrentCompositionProducerProgram.value,CurrentCompositionCertificate.certificate,
  CurrentCompositionCertificate.numeralValues,K,S,values,actualValues,nums,nums',leftArgs,leftArgs',rightArgs,rightArgs',codes,codes'] at hout ⊢
 exact hout

theorem actual {arity k m n ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX))
 (f : Program n) (g : Fin n → Program m) (F : Program (n+1)) (G : Fin n → Program (m+1))
 (J : CurrentCompositionProducerProgram.Tags n) (H : CurrentCompositionProducerProgram.Installation p f g F G J)
 (target producerTag : Nat) (ht : (nodes p)[target]? = some ⟨m,Program.composition f g⟩)
 (hp : (nodes p)[producerTag]? = some ⟨m+1,CurrentCompositionProducerProgram.program f g F G⟩)
 (inputs : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (producerCode producerTag target inputs)
   (CurrentCompositionCertificate.certificate I.previous f g target inputs (childValues f g target inputs)
    (call (target+1) (childValues f g target inputs))
    (List.Vector.ofFn (fun i => producerCode (J.argumentProducerTags i) (target+argumentTag f g i) inputs))
    (producerCode J.functionProducerTag (target+1) (childValues f g target inputs))))) := by
 obtain ⟨hg⟩ := CurrentCompositionProducerProgram.StatementChecks.exactInternal arity p m n f g F G J producerTag H hp ctx (Term.numeral target) inputs
 obtain ⟨hv⟩ := value p installed lhs rhs t old a baseX I f g F G J H target ht inputs
 exact ⟨Logic.trans _ _ _ hg hv⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.CodeBridge
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.CodeBridge
