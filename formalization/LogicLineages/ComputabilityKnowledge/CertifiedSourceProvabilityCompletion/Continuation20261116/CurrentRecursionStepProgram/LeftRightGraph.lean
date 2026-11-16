module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.TemplateGraph
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.LeftRightGraph
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence FixedFormulaSubstitution GorbowRegistryTuple
open SixSol20261112.Fuel NamedArithmeticGraph
open EncodingSupport

theorem shiftedArguments {arity m ctx : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hn : (nodes p)[J.ntag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (target : Term ctx) (inputs : List.Vector (Term ctx) m) (offset : Nat) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag (PrescribedRuntimeSpecialization.runtimeEnvironment (m+1))
    (CurrentRecursionBaseProgram.rawValues (baseTags J) target inputs)
    (CurrentRecursionBaseProgram.openCall (shiftTerm offset (.var (Fin.last m)))
     (List.Vector.ofFn (fun i : Fin m => .var i.castSucc))))
   (callValue (CurrentCalculationFormulaProgram.codecTags J.ctag J.atag J.ntag) (shiftTerm offset target)
    (inputs.map (LiteralNumeralPrefix.numeralCall J.ntag))))) := by
 let K := CurrentCalculationFormulaProgram.codecTags J.ctag J.atag J.ntag
 have hlast : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag (PrescribedRuntimeSpecialization.runtimeEnvironment (m+1))
   (CurrentRecursionBaseProgram.rawValues (baseTags J) target inputs) (.var (Fin.last m)))
   (LiteralNumeralPrefix.numeralCall J.ntag target)) := by
   have htag := CurrentRecursionBaseProgram.CallGraphProof.lastValue (baseTags J) target inputs
   dsimp only [baseTags] at htag
   exact Eq.mpr (congrArg (fun t => Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal t (LiteralNumeralPrefix.numeralCall J.ntag target))) htag) (.logical (.reflexive _))
 obtain ⟨hs⟩ := shiftEncoding p K hc hn _ _ _ target hlast offset
 apply CurrentRecursionBaseProgram.CallGraphProof.dynamicCall p K hc ha _ _ _ _ _ _ hs
 have he := CurrentCompositionCertificate.CallEncodingProof.tupleMap (J := K)
  (PrescribedRuntimeSpecialization.runtimeEnvironment (m+1))
  (CurrentRecursionBaseProgram.rawValues (baseTags J) target inputs)
  (List.Vector.ofFn (fun i : Fin m => (Term.var i.castSucc : Term (m+1)))).toList
 dsimp only [K,CurrentCalculationFormulaProgram.codecTags] at he ⊢
 have hmap := CurrentRecursionBaseProgram.CallGraphProof.inputsMap (baseTags J) target inputs
 dsimp only [baseTags] at hmap
 rw [← List.Vector.toList_map] at he
 have hmapped := congrArg (fun v : List.Vector (Term ctx) m => tupleValue K v.toList) hmap
 dsimp only [K,CurrentCalculationFormulaProgram.codecTags,baseTags] at he hmapped
 have heq := he.trans hmapped
 exact Eq.mpr (congrArg (fun t => Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal t (tupleValue K (inputs.map (LiteralNumeralPrefix.numeralCall J.ntag)).toList))) heq)
  (.logical (.reflexive _))

theorem left {arity m ctx : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hn : (nodes p)[J.ntag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (target counter : Term ctx) (inputs : List.Vector (Term ctx) m) (offset : Nat) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag (PrescribedRuntimeSpecialization.runtimeEnvironment (m+2))
    (CurrentRecursionBaseProgram.rawValues (baseTags J) target (counter ::ᵥ inputs)) (leftTemplate m offset))
   (callValue (CurrentCalculationFormulaProgram.codecTags J.ctag J.atag J.ntag) (shiftTerm offset target)
    (LiteralNumeralPrefix.numeralCall J.ntag counter ::ᵥ
     callValue (CurrentCalculationFormulaProgram.codecTags J.ctag J.atag J.ntag) target
      (LiteralNumeralPrefix.numeralCall J.ntag counter ::ᵥ inputs.map (LiteralNumeralPrefix.numeralCall J.ntag)) ::ᵥ
     inputs.map (LiteralNumeralPrefix.numeralCall J.ntag))))) := by
 let K := CurrentCalculationFormulaProgram.codecTags J.ctag J.atag J.ntag
 have hlast : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag (PrescribedRuntimeSpecialization.runtimeEnvironment (m+2))
   (CurrentRecursionBaseProgram.rawValues (baseTags J) target (counter ::ᵥ inputs)) (.var (Fin.last (m+1))))
   (LiteralNumeralPrefix.numeralCall J.ntag target)) := by
  have htag := CurrentRecursionBaseProgram.CallGraphProof.lastValue (baseTags J) target (counter ::ᵥ inputs)
  dsimp only [baseTags] at htag
  exact Eq.mpr (congrArg (fun t => Derivation (GorbowPRNumeralCalculation.Theory p)
   (.equal t (LiteralNumeralPrefix.numeralCall J.ntag target))) htag) (.logical (.reflexive _))
 obtain ⟨htag⟩ := shiftEncoding p K hc hn _ _ _ target hlast offset
 obtain ⟨hprior⟩ := TemplateGraph.prior p J hc ha target counter inputs
 obtain ⟨htail⟩ := tupleCons p K hc ha _ _ _ _ hprior
  (.logical (.reflexive (tupleValue K (inputs.map (LiteralNumeralPrefix.numeralCall J.ntag)).toList)))
 have hcounter : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag (PrescribedRuntimeSpecialization.runtimeEnvironment (m+2))
   (CurrentRecursionBaseProgram.rawValues (baseTags J) target (counter ::ᵥ inputs)) (.var 0))
   (LiteralNumeralPrefix.numeralCall J.ntag counter)) := by
  rw [counterValue]
  exact .logical (.reflexive _)
 obtain ⟨htuple⟩ := tupleCons p K hc ha _ _ _ _ hcounter htail
 apply CurrentRecursionBaseProgram.CallGraphProof.dynamicCall p K hc ha _ _ _ _ _ _ htag
 have he := CurrentCompositionCertificate.CallEncodingProof.tupleMap (J := K)
    (PrescribedRuntimeSpecialization.runtimeEnvironment (m+2))
    (CurrentRecursionBaseProgram.rawValues (baseTags J) target (counter ::ᵥ inputs))
    (.var 0 ::ᵥ priorTemplate m ::ᵥ params m).toList
 dsimp only [K,CurrentCalculationFormulaProgram.codecTags] at he ⊢
 rw [← List.Vector.toList_map,List.Vector.map_cons,List.Vector.map_cons,paramsMap] at he
 rw [he]
 exact htuple
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.LeftRightGraph
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.LeftRightGraph
