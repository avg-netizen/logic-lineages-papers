module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.StepOperands
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.OpenStepCode
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.UnaryCopy
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.StepUnary
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph

open CurrentRecursionStepCertificate CurrentEqualityImplication
theorem certificate {arity k m ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX))
 (base : Program m) (step : Program (m+2)) (B : Program (m+1)) (G : Program (m+3))
 (R : CurrentRecursionProducerSource.Installation p installed lhs rhs t old a baseX base step B G)
 (counter : Term ctx) (inputs : List.Vector (Term ctx) m) :
 let C := CurrentCalculationFormulaProgram.codecTags R.SJ.ctag R.SJ.atag R.SJ.ntag
 let J := tags I.previous
 let srcRaw := (counter ::ᵥ inputs).map (LiteralNumeralPrefix.numeralCall C.numeralTag)
 let dstRaw := (counter ::ᵥ inputs).map (LiteralNumeralPrefix.numeralCall J.numeralTag)
 let prior := callValue C (Term.numeral R.qTag) srcRaw
 let previous := LiteralNumeralPrefix.numeralCall C.numeralTag (call R.SJ.qtag (counter ::ᵥ inputs))
 let prior' := callValue J (Term.numeral R.qTag) dstRaw
 let previous' := LiteralNumeralPrefix.numeralCall J.numeralTag (call R.qTag (counter ::ᵥ inputs))
 let openCode := FixedFormulaSubstitution.termValue R.SJ.ctag R.SJ.atag (PrescribedRuntimeSpecialization.headEnvironment (m+2))
  (CurrentRecursionBaseProgram.rawValues (CurrentRecursionStepProgram.baseTags R.SJ) (Term.numeral R.qTag) (counter ::ᵥ inputs))
  (CurrentRecursionStepProgram.unaryTemplate m (GorbowPRChildTags.stepTag base))
 let target := CurrentRecursionStepProgram.shiftTerm (GorbowPRChildTags.stepTag base) (Term.numeral R.qTag)
 let left := callValue C target (LiteralNumeralPrefix.numeralCall C.numeralTag counter ::ᵥ prior ::ᵥ inputs.map (LiteralNumeralPrefix.numeralCall C.numeralTag))
 let right := callValue C target (LiteralNumeralPrefix.numeralCall C.numeralTag counter ::ᵥ previous ::ᵥ inputs.map (LiteralNumeralPrefix.numeralCall C.numeralTag))
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (CurrentRecursionStepProgram.unaryValue R.SJ openCode prior previous left right)
   (unaryRuleCertificate I (stepEnvironment m) (stepTemplate m (R.qTag+GorbowPRChildTags.stepTag base)) dstRaw prior' previous'))) := by
 dsimp only
 let C := CurrentCalculationFormulaProgram.codecTags R.SJ.ctag R.SJ.atag R.SJ.ntag
 let J := tags I.previous
 let raw := (counter ::ᵥ inputs).map (LiteralNumeralPrefix.numeralCall J.numeralTag)
 let prior' := callValue J (Term.numeral R.qTag) raw
 let previous' := LiteralNumeralPrefix.numeralCall J.numeralTag (call R.qTag (counter ::ᵥ inputs))
 have hC : CodecBridge.Nodes p C := ⟨R.stepInstallation.hc,R.stepInstallation.ha,R.stepInstallation.hn⟩
 have hJ := FormulaBridge.originalNodes p installed lhs rhs t old a _ I
 obtain ⟨hprior⟩ := CodecBridge.call p C J hC hJ (Term.numeral R.qTag) (counter ::ᵥ inputs)
 obtain ⟨hprevious⟩ := CodecBridge.numeral p C J hC hJ (call R.qTag (counter ::ᵥ inputs))
 have hnums (i : Fin (m+1)) := CodecBridge.numeral p C J hC hJ ((counter ::ᵥ inputs).get i)
 obtain ⟨hnums⟩ := SpecializationCopy.finiteWitness (m+1) (fun i => Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralNumeralPrefix.numeralCall C.numeralTag ((counter ::ᵥ inputs).get i))
   (LiteralNumeralPrefix.numeralCall J.numeralTag ((counter ::ᵥ inputs).get i)))) hnums
 obtain ⟨hopen⟩ := OpenStepCode.term p (CurrentRecursionStepProgram.baseTags R.SJ) J.ctag J.atag
  R.stepInstallation.hc R.stepInstallation.ha R.stepInstallation.hn hJ.hc hJ.ha
  (GorbowPRChildTags.stepTag base) R.qTag (counter ::ᵥ inputs) raw (fun i => by
   simp only [raw,List.Vector.get_map]
   exact hnums i)
 obtain ⟨hleft⟩ := StepOperands.left p installed lhs rhs t old a baseX I base step B G R counter inputs
 obtain ⟨hright⟩ := StepOperands.right p installed lhs rhs t old a baseX I base step B G R counter inputs
 obtain ⟨hft⟩ := SymbolicProof.stepValue p J hJ.hc hJ.ha hJ.hn (R.qTag+GorbowPRChildTags.stepTag base)
  (LiteralNumeralPrefix.numeralCall J.numeralTag counter) prior' (inputs.map (LiteralNumeralPrefix.numeralCall J.numeralTag))
 obtain ⟨hfu⟩ := SymbolicProof.stepValue p J hJ.hc hJ.ha hJ.hn (R.qTag+GorbowPRChildTags.stepTag base)
  (LiteralNumeralPrefix.numeralCall J.numeralTag counter) previous' (inputs.map (LiteralNumeralPrefix.numeralCall J.numeralTag))
 have h := UnaryCopy.certificate p installed lhs rhs t old a _ I base step G R.SJ R.stepInstallation
  (stepEnvironment m) (stepTemplate m (R.qTag+GorbowPRChildTags.stepTag base)) raw _ _ _ _ _ prior' previous'
  hopen hprior hprevious (Logic.trans _ _ _ hleft (NamedArithmeticGraph.Support.equalitySymmetry _ _ hft)) (Logic.trans _ _ _ hright (NamedArithmeticGraph.Support.equalitySymmetry _ _ hfu))
 simp only [R.recursionAddress,raw,prior',previous',List.Vector.map_cons,C,J,CurrentRecursionStepProgram.baseTags,CurrentCalculationFormulaProgram.codecTags] at h ⊢
 exact h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.StepUnary
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.StepUnary
