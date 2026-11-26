module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.EncodingSupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.TemplateGraph
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence FixedFormulaSubstitution GorbowRegistryTuple
open SixSol20261112.Fuel NamedArithmeticGraph
open EncodingSupport

theorem oneHead {arity m ctx : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (target counter : Term ctx) (inputs : List.Vector (Term ctx) m) (t : Term (m+2)) (v : Term ctx)
 (h : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag (PrescribedRuntimeSpecialization.runtimeEnvironment (m+2))
   (CurrentRecursionBaseProgram.rawValues (baseTags J) target (counter ::ᵥ inputs)) t) v)) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag (PrescribedRuntimeSpecialization.runtimeEnvironment (m+2))
    (CurrentRecursionBaseProgram.rawValues (baseTags J) target (counter ::ᵥ inputs))
    (CurrentRecursionBaseProgram.openCall (.var (Fin.last (m+1))) (t ::ᵥ params m)))
   (callValue (CurrentCalculationFormulaProgram.codecTags J.ctag J.atag J.ntag) target
    (v ::ᵥ inputs.map (LiteralNumeralPrefix.numeralCall J.ntag))))) := by
 let K := CurrentCalculationFormulaProgram.codecTags J.ctag J.atag J.ntag
 obtain ⟨htuple⟩ := tupleCons p K hc ha _ _ _ _ h
  (.logical (.reflexive (tupleValue K (inputs.map (LiteralNumeralPrefix.numeralCall J.ntag)).toList)))
 apply CurrentRecursionBaseProgram.CallGraphProof.dynamicCall p K hc ha _ _ _ _ _ _
 · have ht := CurrentRecursionBaseProgram.CallGraphProof.lastValue (baseTags J) target (counter ::ᵥ inputs)
   dsimp only [K,CurrentCalculationFormulaProgram.codecTags,baseTags] at ht ⊢
   rw [ht]
   exact .logical (.reflexive _)
 · have he := CurrentCompositionCertificate.CallEncodingProof.tupleMap (J := K)
    (PrescribedRuntimeSpecialization.runtimeEnvironment (m+2))
    (CurrentRecursionBaseProgram.rawValues (baseTags J) target (counter ::ᵥ inputs)) (t ::ᵥ params m).toList
   dsimp only [K,CurrentCalculationFormulaProgram.codecTags] at he ⊢
   rw [← List.Vector.toList_map,List.Vector.map_cons,paramsMap] at he
   rw [he]
   exact htuple

theorem prior {arity m ctx : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (target counter : Term ctx) (inputs : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag (PrescribedRuntimeSpecialization.runtimeEnvironment (m+2))
    (CurrentRecursionBaseProgram.rawValues (baseTags J) target (counter ::ᵥ inputs)) (priorTemplate m))
   (callValue (CurrentCalculationFormulaProgram.codecTags J.ctag J.atag J.ntag) target
    (LiteralNumeralPrefix.numeralCall J.ntag counter ::ᵥ inputs.map (LiteralNumeralPrefix.numeralCall J.ntag))))) := by
 apply oneHead p J hc ha target counter inputs (.var 0) _
 rw [counterValue]
 exact .logical (.reflexive _)

theorem next {arity m ctx : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hn : (nodes p)[J.ntag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (target counter : Term ctx) (inputs : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag (PrescribedRuntimeSpecialization.runtimeEnvironment (m+2))
    (CurrentRecursionBaseProgram.rawValues (baseTags J) target (counter ::ᵥ inputs)) (nextTemplate m))
   (callValue (CurrentCalculationFormulaProgram.codecTags J.ctag J.atag J.ntag) target
    (LiteralNumeralPrefix.numeralCall J.ntag (.succ counter) ::ᵥ inputs.map (LiteralNumeralPrefix.numeralCall J.ntag))))) := by
 obtain ⟨hs⟩ := LiteralNumeralPrefix.EquationsProof.successor p J.ntag J.ctag hn hc counter
 apply oneHead p J hc ha target counter inputs (.succ (.var 0)) _
 change Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (FixedFormulaSubstitution.unaryValue J.ctag 2
   (termValue J.ctag J.atag (PrescribedRuntimeSpecialization.runtimeEnvironment (m+2))
    (CurrentRecursionBaseProgram.rawValues (baseTags J) target (counter ::ᵥ inputs)) (.var 0)))
   (LiteralNumeralPrefix.numeralCall J.ntag (.succ counter)))
 rw [counterValue]
 exact Support.equalitySymmetry _ _ hs
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.TemplateGraph
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.TemplateGraph
