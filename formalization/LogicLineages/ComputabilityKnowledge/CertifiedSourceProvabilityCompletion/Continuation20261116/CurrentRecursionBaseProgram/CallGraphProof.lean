module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.GraphInputs
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.CallGraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open FixedFormulaSubstitution GorbowRegistryTuple

theorem dynamicCall {arity n inputs ctx m : Nat} (p : Program arity) (J : PrescribedRuntimeCallCongruence.Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (e : Environment n 0 inputs) (raw : List.Vector (Term ctx) inputs) (s : Term n) (target : Term ctx)
 (args : List.Vector (Term n) m) (values : List.Vector (Term ctx) m)
 (ht : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (termValue J.ctag J.atag e raw s) (LiteralNumeralPrefix.numeralCall J.numeralTag target)))
 (hv : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (termValue J.ctag J.atag e raw (tupleTerm args.toList)) (tupleValue J values.toList))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag e raw (openCall s args)) (callValue J target values))) := by
 obtain ⟨hn⟩ := CurrentCompositionCertificate.CallEncodingProof.numeral p J.ctag J.atag hc e raw m
 obtain ⟨hp⟩ := CurrentCompositionCertificate.CallEncodingProof.pairCongruence p J hc ha _ _ _ _ ht hv
 obtain ⟨hh⟩ := CurrentCompositionCertificate.CallEncodingProof.pairCongruence p J hc ha _ _ _ _ hn hp
 obtain ⟨hu⟩ := CurrentCompositionCertificate.CodecProof.unary p J.ctag J.ctag 5 hc hc _ _ hh
 simpa only [openCall,termValue,CurrentCompositionCertificate.CallEncodingProof.pairMap,callValue,headerValue] using (show Nonempty _ from ⟨hu⟩)

theorem inputsMap {m ctx : Nat} (J : Tags) (target : Term ctx) (inputs : List.Vector (Term ctx) m) :
 (List.Vector.ofFn (fun i : Fin m => (Term.var i.castSucc : Term (m+1)))).map
  (termValue J.ctag J.atag (PrescribedRuntimeSpecialization.runtimeEnvironment (m+1)) (rawValues J target inputs)) =
 inputs.map (LiteralNumeralPrefix.numeralCall J.ntag) := by
 ext i
 simp only [List.Vector.get_map,List.Vector.get_ofFn,termValue,PrescribedRuntimeSpecialization.runtimeEnvironment,
  rawValues,Fin.lastCases_castSucc]

theorem lastValue {m ctx : Nat} (J : Tags) (target : Term ctx) (inputs : List.Vector (Term ctx) m) :
 termValue J.ctag J.atag (PrescribedRuntimeSpecialization.runtimeEnvironment (m+1)) (rawValues J target inputs) (.var (Fin.last m)) =
 LiteralNumeralPrefix.numeralCall J.ntag target := by
 simp only [termValue,PrescribedRuntimeSpecialization.runtimeEnvironment,rawValues,List.Vector.get_ofFn,Fin.lastCases_last]

theorem childValue {arity m ctx : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hn : (nodes p)[J.ntag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (target : Term ctx) (inputs : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag (PrescribedRuntimeSpecialization.runtimeEnvironment (m+1)) (rawValues J target inputs)
   (openCall (.succ (.var (Fin.last m))) (List.Vector.ofFn (fun i : Fin m => (Term.var i.castSucc : Term (m+1))))))
   (callValue (CurrentCalculationFormulaProgram.codecTags J.ctag J.atag J.ntag) (.succ target) (inputs.map (LiteralNumeralPrefix.numeralCall J.ntag))))) := by
 let K := CurrentCalculationFormulaProgram.codecTags J.ctag J.atag J.ntag
 obtain ⟨hs⟩ := LiteralNumeralPrefix.EquationsProof.successor p J.ntag J.ctag hn hc target
 apply dynamicCall p K hc ha _ _ _ _ _ _
 · simpa only [K,CurrentCalculationFormulaProgram.codecTags,termValue,FixedFormulaSubstitution.unaryValue,
    PrescribedRuntimeSpecialization.runtimeEnvironment,rawValues,List.Vector.get_ofFn,Fin.lastCases_last]
    using Support.equalitySymmetry _ _ hs
 · have he := CurrentCompositionCertificate.CallEncodingProof.tupleMap (J := K)
    (PrescribedRuntimeSpecialization.runtimeEnvironment (m+1)) (rawValues J target inputs)
    (List.Vector.ofFn (fun i : Fin m => (Term.var i.castSucc : Term (m+1)))).toList
   dsimp only [K,CurrentCalculationFormulaProgram.codecTags] at he ⊢
   rw [← List.Vector.toList_map,inputsMap] at he
   rw [he]
   exact .logical (.reflexive _)

theorem parentValue {arity m ctx : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hn : (nodes p)[J.ntag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (target : Term ctx) (inputs : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag (PrescribedRuntimeSpecialization.runtimeEnvironment (m+1)) (rawValues J target inputs)
   (openCall (.var (Fin.last m)) (.zero ::ᵥ List.Vector.ofFn (fun i : Fin m => (Term.var i.castSucc : Term (m+1))))))
   (callValue (CurrentCalculationFormulaProgram.codecTags J.ctag J.atag J.ntag) target
    (LiteralNumeralPrefix.numeralCall J.ntag .zero ::ᵥ inputs.map (LiteralNumeralPrefix.numeralCall J.ntag))))) := by
 let K := CurrentCalculationFormulaProgram.codecTags J.ctag J.atag J.ntag
 obtain ⟨hz⟩ := ValueTraceProof.numeral (ctx := ctx) p K hn 0
 have hzero := Support.equalitySymmetry _ _ hz
 have hp := CurrentCompositionCertificate.CallEncodingProof.pairCongruence p K hc ha _ _ _ _ hzero
  (.logical (.reflexive (tupleValue K (inputs.map (LiteralNumeralPrefix.numeralCall J.ntag)).toList)))
 obtain ⟨hp⟩ := hp
 obtain ⟨htuple⟩ := CurrentCompositionCertificate.CodecProof.unary p J.ctag J.ctag 2 hc hc _ _ hp
 apply dynamicCall p K hc ha _ _ _ _ _ _
 · dsimp only [K,CurrentCalculationFormulaProgram.codecTags]
   rw [lastValue]
   exact .logical (.reflexive _)
 · have he := CurrentCompositionCertificate.CallEncodingProof.tupleMap (J := K)
    (PrescribedRuntimeSpecialization.runtimeEnvironment (m+1)) (rawValues J target inputs)
    (.zero ::ᵥ List.Vector.ofFn (fun i : Fin m => (Term.var i.castSucc : Term (m+1)))).toList
   dsimp only [K,CurrentCalculationFormulaProgram.codecTags] at he ⊢
   rw [← List.Vector.toList_map,List.Vector.map_cons,inputsMap] at he
   rw [he]
   exact htuple
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.CallGraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.CallGraphProof
