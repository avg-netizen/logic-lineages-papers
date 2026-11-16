module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.StepUnary
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.StepSeed
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.StepAssembly
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.StepCode
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph

open CurrentRecursionStepCertificate CurrentEqualityImplication
theorem value {arity k m ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX))
 (base : Program m) (step : Program (m+2)) (B : Program (m+1)) (G : Program (m+3))
 (R : CurrentRecursionProducerSource.Installation p installed lhs rhs t old a baseX base step B G)
 (counter : Term ctx) (inputs : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (CurrentRecursionStepProgram.value base R.SJ (Term.numeral R.qTag) counter inputs)
   (CurrentRecursionStepCertificate.certificate I base R.qTag counter inputs
    (call R.qTag (counter ::ᵥ inputs))
    (call (R.qTag+GorbowPRChildTags.stepTag base) (stepInputs R.qTag counter inputs))
    (childCode R.GTag (R.qTag+GorbowPRChildTags.stepTag base) (stepInputs R.qTag counter inputs))))) := by
 let C := CurrentCalculationFormulaProgram.codecTags R.SJ.ctag R.SJ.atag R.SJ.ntag
 let J := tags I.previous
 let raw := (counter ::ᵥ inputs).map (LiteralNumeralPrefix.numeralCall J.numeralTag)
 let K : CurrentRecursionBaseProgram.Tags :=
  { ptag := R.SJ.ptag
    ctag := I.previous.previous.current.ctag
    atag := I.previous.previous.current.atag
    ntag := J.numeralTag
    mtag := J.mtag
    r12 := J.constructorTag
    r13 := I.previous.previous.current.constructorTag
    baseTag := R.SJ.qtag
    childTag := R.SJ.childTag }
 have hC : CodecBridge.Nodes p C := ⟨R.stepInstallation.hc,R.stepInstallation.ha,R.stepInstallation.hn⟩
 have hJ := FormulaBridge.originalNodes p installed lhs rhs t old a _ I
 have hm := I.previous.previous.previous.previous.previous.hmp
 obtain ⟨hprior⟩ := CodecBridge.call p C J hC hJ (Term.numeral R.qTag) (counter ::ᵥ inputs)
 obtain ⟨hprevious⟩ := CodecBridge.numeral p C J hC hJ (call R.qTag (counter ::ᵥ inputs))
 obtain ⟨hP⟩ := CurrentCompositionCertificate.CodecProof.binary p C.ctag C.atag J.ctag J.atag 0 hC.hc hC.ha hJ.hc hJ.ha
  _ _ _ _ hprior hprevious
 obtain ⟨hnext⟩ := CodecBridge.call p C J hC hJ (Term.numeral R.qTag) (.succ counter ::ᵥ inputs)
 obtain ⟨hleft⟩ := StepOperands.left p installed lhs rhs t old a baseX I base step B G R counter inputs
 obtain ⟨hright⟩ := StepOperands.right p installed lhs rhs t old a baseX I base step B G R counter inputs
 obtain ⟨houtput⟩ := CodecBridge.numeral p C J hC hJ
  (call (R.qTag+GorbowPRChildTags.stepTag base) (stepInputs R.qTag counter inputs))
 have hnums (i : Fin (m+1)) := CodecBridge.numeral p C J hC hJ ((counter ::ᵥ inputs).get i)
 obtain ⟨hnums⟩ := SpecializationCopy.finiteWitness (m+1) (fun i => Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralNumeralPrefix.numeralCall C.numeralTag ((counter ::ᵥ inputs).get i))
   (LiteralNumeralPrefix.numeralCall J.numeralTag ((counter ::ᵥ inputs).get i)))) hnums
 obtain ⟨hseed⟩ := StepSeed.certificate p (CurrentRecursionStepProgram.baseTags R.SJ) K
  R.stepInstallation.hp R.stepInstallation.hc R.stepInstallation.ha R.stepInstallation.hm R.stepInstallation.h13 R.stepInstallation.hn
  I.previous.previous.current.h_ctag I.previous.previous.current.h_atag hm I.previous.previous.current.h_constructor
  base R.qTag (counter ::ᵥ inputs) raw (fun i => by simpa only [raw,List.Vector.get_map] using hnums i)
 obtain ⟨hunary⟩ := StepUnary.certificate p installed lhs rhs t old a baseX I base step B G R counter inputs
 have hchild : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call R.SJ.childTag (CurrentRecursionStepProgram.shiftTerm (GorbowPRChildTags.stepTag base) (Term.numeral R.qTag) ::ᵥ
    counter ::ᵥ call R.SJ.qtag (counter ::ᵥ inputs) ::ᵥ inputs))
   (childCode R.GTag (R.qTag+GorbowPRChildTags.stepTag base) (stepInputs R.qTag counter inputs))) := by
  rw [CurrentRecursionStepProgram.TemplateSyntax.shiftNumeral,R.stepChildAddress,R.recursionAddress]
  exact .logical (.reflexive _)
 have h := StepAssembly.assemble p installed lhs rhs t old a _ I base step G R.SJ R.stepInstallation
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP hnext hleft hright houtput hseed hunary hchild
 simpa only [CurrentRecursionStepProgram.value,CurrentRecursionStepCertificate.certificate,
  CurrentCompositionCertificate.numeralValues,CurrentRecursionBaseCertificate.numeralValues,
  R.recursionAddress,R.stepAddress,CurrentRecursionStepProgram.TemplateSyntax.shiftNumeral,
  stepInputs,List.Vector.map_cons,C,J,K,raw] using h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.StepCode
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.StepCode
