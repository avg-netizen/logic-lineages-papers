module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.CallRawCopy
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.FormulaBridge
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.SpecializationCopy
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.StepOperands
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph

theorem left {arity k m ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX))
 (base : Program m) (step : Program (m+2)) (B : Program (m+1)) (G : Program (m+3))
 (R : CurrentRecursionProducerSource.Installation p installed lhs rhs t old a baseX base step B G)
 (counter : Term ctx) (inputs : List.Vector (Term ctx) m) :
 let C := CurrentCalculationFormulaProgram.codecTags R.SJ.ctag R.SJ.atag R.SJ.ntag
 let J := tags I.previous
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (callValue C (CurrentRecursionStepProgram.shiftTerm (GorbowPRChildTags.stepTag base) (Term.numeral R.qTag))
    (LiteralNumeralPrefix.numeralCall C.numeralTag counter ::ᵥ (callValue C (Term.numeral R.qTag) ((counter ::ᵥ inputs).map (LiteralNumeralPrefix.numeralCall C.numeralTag))) ::ᵥ inputs.map (LiteralNumeralPrefix.numeralCall C.numeralTag)))
   (callValue J (Term.numeral (R.qTag+GorbowPRChildTags.stepTag base))
    (LiteralNumeralPrefix.numeralCall J.numeralTag counter ::ᵥ (callValue J (Term.numeral R.qTag) ((counter ::ᵥ inputs).map (LiteralNumeralPrefix.numeralCall J.numeralTag))) ::ᵥ inputs.map (LiteralNumeralPrefix.numeralCall J.numeralTag))))) := by
 dsimp only
 let C := CurrentCalculationFormulaProgram.codecTags R.SJ.ctag R.SJ.atag R.SJ.ntag
 let J := tags I.previous
 have hC : CodecBridge.Nodes p C := ⟨R.stepInstallation.hc,R.stepInstallation.ha,R.stepInstallation.hn⟩
 have hJ := FormulaBridge.originalNodes p installed lhs rhs t old a _ I
 obtain ⟨hcounter⟩ := CodecBridge.numeral p C J hC hJ counter
 obtain ⟨hmiddle⟩ := CodecBridge.call p C J hC hJ (Term.numeral R.qTag) (counter ::ᵥ inputs)
 have hnums (i : Fin m) := CodecBridge.numeral p C J hC hJ (inputs.get i)
 obtain ⟨hnums⟩ := SpecializationCopy.finiteWitness m (fun i => Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralNumeralPrefix.numeralCall C.numeralTag (inputs.get i))
   (LiteralNumeralPrefix.numeralCall J.numeralTag (inputs.get i)))) hnums
 have hcopy := CallRawCopy.call p C J hC hJ (Term.numeral (R.qTag+GorbowPRChildTags.stepTag base))
  (LiteralNumeralPrefix.numeralCall C.numeralTag counter ::ᵥ _ ::ᵥ inputs.map (LiteralNumeralPrefix.numeralCall C.numeralTag))
  (LiteralNumeralPrefix.numeralCall J.numeralTag counter ::ᵥ _ ::ᵥ inputs.map (LiteralNumeralPrefix.numeralCall J.numeralTag)) (fun i => by
   cases i using Fin.cases with
   | zero => exact hcounter
   | succ i => cases i using Fin.cases with
     | zero => exact hmiddle
     | succ i => simpa only [List.Vector.get_cons_succ,List.Vector.get_map] using hnums i)
 simp only [CurrentRecursionStepProgram.TemplateSyntax.shiftNumeral,R.recursionAddress,C,J,CurrentCalculationFormulaProgram.codecTags] at hcopy ⊢
 exact hcopy

theorem right {arity k m ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX))
 (base : Program m) (step : Program (m+2)) (B : Program (m+1)) (G : Program (m+3))
 (R : CurrentRecursionProducerSource.Installation p installed lhs rhs t old a baseX base step B G)
 (counter : Term ctx) (inputs : List.Vector (Term ctx) m) :
 let C := CurrentCalculationFormulaProgram.codecTags R.SJ.ctag R.SJ.atag R.SJ.ntag
 let J := tags I.previous
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (callValue C (CurrentRecursionStepProgram.shiftTerm (GorbowPRChildTags.stepTag base) (Term.numeral R.qTag))
    (LiteralNumeralPrefix.numeralCall C.numeralTag counter ::ᵥ (LiteralNumeralPrefix.numeralCall C.numeralTag (call R.SJ.qtag (counter ::ᵥ inputs))) ::ᵥ inputs.map (LiteralNumeralPrefix.numeralCall C.numeralTag)))
   (callValue J (Term.numeral (R.qTag+GorbowPRChildTags.stepTag base))
    (LiteralNumeralPrefix.numeralCall J.numeralTag counter ::ᵥ (LiteralNumeralPrefix.numeralCall J.numeralTag (call R.qTag (counter ::ᵥ inputs))) ::ᵥ inputs.map (LiteralNumeralPrefix.numeralCall J.numeralTag))))) := by
 dsimp only
 let C := CurrentCalculationFormulaProgram.codecTags R.SJ.ctag R.SJ.atag R.SJ.ntag
 let J := tags I.previous
 have hC : CodecBridge.Nodes p C := ⟨R.stepInstallation.hc,R.stepInstallation.ha,R.stepInstallation.hn⟩
 have hJ := FormulaBridge.originalNodes p installed lhs rhs t old a _ I
 obtain ⟨hcounter⟩ := CodecBridge.numeral p C J hC hJ counter
 obtain ⟨hmiddle⟩ := CodecBridge.numeral p C J hC hJ (call R.qTag (counter ::ᵥ inputs))
 have hnums (i : Fin m) := CodecBridge.numeral p C J hC hJ (inputs.get i)
 obtain ⟨hnums⟩ := SpecializationCopy.finiteWitness m (fun i => Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralNumeralPrefix.numeralCall C.numeralTag (inputs.get i))
   (LiteralNumeralPrefix.numeralCall J.numeralTag (inputs.get i)))) hnums
 have hcopy := CallRawCopy.call p C J hC hJ (Term.numeral (R.qTag+GorbowPRChildTags.stepTag base))
  (LiteralNumeralPrefix.numeralCall C.numeralTag counter ::ᵥ _ ::ᵥ inputs.map (LiteralNumeralPrefix.numeralCall C.numeralTag))
  (LiteralNumeralPrefix.numeralCall J.numeralTag counter ::ᵥ _ ::ᵥ inputs.map (LiteralNumeralPrefix.numeralCall J.numeralTag)) (fun i => by
   cases i using Fin.cases with
   | zero => exact hcounter
   | succ i => cases i using Fin.cases with
     | zero => exact hmiddle
     | succ i => simpa only [List.Vector.get_cons_succ,List.Vector.get_map] using hnums i)
 simp only [CurrentRecursionStepProgram.TemplateSyntax.shiftNumeral,R.recursionAddress,C,J,CurrentCalculationFormulaProgram.codecTags] at hcopy ⊢
 exact hcopy

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.StepOperands
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.StepOperands
