module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.CodecBridge
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.FormulaBridge
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph

theorem originalNodes {arity k : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x) :
 CodecBridge.Nodes p (tags I.previous) :=
 ⟨I.previous.current.h_ctag,I.previous.current.h_atag,I.previous.previous.previous.previous.previous.hnumeral⟩

theorem actualFormula {arity k m ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX))
 (base : Program m) (step : Program (m+2)) (B : Program (m+1)) (G : Program (m+3))
 (R : CurrentRecursionProducerSource.Installation p installed lhs rhs t old a baseX base step B G)
 (counter : Term ctx) (inputs : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (formulaCall R.producer.formulaTag R.qTag counter inputs)
   (childFormula (tags I.previous) R.qTag (counter ::ᵥ inputs)))) := by
 let K := CurrentCalculationFormulaProgram.codecTags R.SJ.ctag R.SJ.atag R.SJ.ntag
 have hK : CodecBridge.Nodes p K := ⟨R.stepInstallation.hc,R.stepInstallation.ha,R.stepInstallation.hn⟩
 obtain ⟨hf⟩ := CurrentCalculationFormulaProgram.StatementChecks.exactInternal arity p (m+1) (.recursion base step)
  R.producer.formulaTag R.qTag R.SJ.ctag R.SJ.atag R.SJ.ntag
  R.producer.hformula R.hQ R.stepInstallation.hc R.stepInstallation.ha R.stepInstallation.hn ctx (Term.numeral R.qTag) (counter ::ᵥ inputs)
 obtain ⟨hc⟩ := CodecBridge.calculation p K (tags I.previous) hK (originalNodes p installed lhs rhs t old a _ I)
  R.qTag (counter ::ᵥ inputs)
 exact ⟨Logic.trans _ _ _ hf hc⟩

theorem changeResult {arity ctx n : Nat} (p : Program arity) (J : PrescribedRuntimeCallCongruence.Tags)
 (tag : Nat) (inputs : List.Vector (Term ctx) n) (result : Term ctx)
 (h : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call tag inputs) result)) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (childFormula J tag inputs)
   (equalValue J.ctag J.atag
    (callValue J (Term.numeral tag) (inputs.map (LiteralNumeralPrefix.numeralCall J.numeralTag)))
    (LiteralNumeralPrefix.numeralCall J.numeralTag result)))) := by
 have hn := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) J.numeralTag
  (call tag inputs ::ᵥ nil) (result ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact h
   | succ i => exact Fin.elim0 i)
 let left := callValue J (Term.numeral tag) (inputs.map (LiteralNumeralPrefix.numeralCall J.numeralTag))
 have ha := HistoryAppend.PositiveProof.binaryCongruence J.atag left left
  (LiteralNumeralPrefix.numeralCall J.numeralTag (call tag inputs)) (LiteralNumeralPrefix.numeralCall J.numeralTag result)
  (.logical (.reflexive left)) hn
 have hc := HistoryAppend.PositiveProof.binaryCongruence J.ctag (Term.numeral 0) (Term.numeral 0) _ _
  (.logical (.reflexive _)) ha
 exact ⟨hc⟩

theorem zero {arity k m ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX))
 (base : Program m) (step : Program (m+2)) (B : Program (m+1)) (G : Program (m+3))
 (R : CurrentRecursionProducerSource.Installation p installed lhs rhs t old a baseX base step B G)
 (inputs : List.Vector (Term ctx) m) :
 let J := tags I.previous
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (formulaCall R.producer.formulaTag R.qTag .zero inputs)
   (equalValue J.ctag J.atag
    (callValue J (Term.numeral R.qTag) ((.zero ::ᵥ inputs).map (LiteralNumeralPrefix.numeralCall J.numeralTag)))
    (LiteralNumeralPrefix.numeralCall J.numeralTag (call (R.qTag+1) inputs))))) := by
 obtain ⟨hf⟩ := actualFormula p installed lhs rhs t old a baseX I base step B G R .zero inputs
 obtain ⟨hz⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation arity p R.qTag m base step R.hQ ctx inputs
 obtain ⟨hc⟩ := changeResult p (tags I.previous) R.qTag (.zero ::ᵥ inputs) _ hz
 exact ⟨Logic.trans _ _ _ hf hc⟩

theorem successor {arity k m ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX))
 (base : Program m) (step : Program (m+2)) (B : Program (m+1)) (G : Program (m+3))
 (R : CurrentRecursionProducerSource.Installation p installed lhs rhs t old a baseX base step B G)
 (counter : Term ctx) (inputs : List.Vector (Term ctx) m) :
 let J := tags I.previous
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (formulaCall R.producer.formulaTag R.qTag (.succ counter) inputs)
   (equalValue J.ctag J.atag
    (callValue J (Term.numeral R.qTag) ((.succ counter ::ᵥ inputs).map (LiteralNumeralPrefix.numeralCall J.numeralTag)))
    (LiteralNumeralPrefix.numeralCall J.numeralTag
     (call (R.qTag+GorbowPRChildTags.stepTag base) (stepInputs R.qTag counter inputs)))))) := by
 obtain ⟨hf⟩ := actualFormula p installed lhs rhs t old a baseX I base step B G R (.succ counter) inputs
 obtain ⟨hs⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation arity p R.qTag m base step R.hQ ctx counter inputs
 obtain ⟨hc⟩ := changeResult p (tags I.previous) R.qTag (.succ counter ::ᵥ inputs) _ hs
 exact ⟨Logic.trans _ _ _ hf hc⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.FormulaBridge
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.FormulaBridge
