module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.EvaluatorGraph
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.EncodingSupport
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence FixedFormulaSubstitution GorbowRegistryTuple
open SixSol20261112.Fuel NamedArithmeticGraph

theorem tupleCons {arity ctx : Nat} (p : Program arity) (J : PrescribedRuntimeCallCongruence.Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (a b : Term ctx) (as bs : List (Term ctx))
 (h : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a b))
 (ht : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (tupleValue J as) (tupleValue J bs))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (tupleValue J (a::as)) (tupleValue J (b::bs)))) := by
 obtain ⟨hp⟩ := CurrentCompositionCertificate.CallEncodingProof.pairCongruence p J hc ha _ _ _ _ h ht
 exact CurrentCompositionCertificate.CodecProof.unary p J.ctag J.ctag 2 hc hc _ _ hp

theorem shiftEncoding {arity n depth inputs ctx : Nat} (p : Program arity) (J : PrescribedRuntimeCallCongruence.Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hn : (nodes p)[J.numeralTag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (e : Environment n depth inputs) (raw : List.Vector (Term ctx) inputs) (t : Term n) (v : Term ctx)
 (h : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag e raw t) (LiteralNumeralPrefix.numeralCall J.numeralTag v))) (offset : Nat) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag e raw (shiftTerm offset t))
   (LiteralNumeralPrefix.numeralCall J.numeralTag (shiftTerm offset v)))) := by
 induction offset with
 | zero => exact ⟨h⟩
 | succ k ih =>
   obtain ⟨ih⟩ := ih
   obtain ⟨hu⟩ := CurrentCompositionCertificate.CodecProof.unary p J.ctag J.ctag 2 hc hc _ _ ih
   obtain ⟨hs⟩ := LiteralNumeralPrefix.EquationsProof.successor p J.numeralTag J.ctag hn hc (shiftTerm k v)
   exact ⟨Logic.trans _ _ _ hu (Support.equalitySymmetry _ _ hs)⟩

theorem paramsMap {m ctx : Nat} (J : Tags) (target counter : Term ctx) (inputs : List.Vector (Term ctx) m) :
 (params m).map (termValue J.ctag J.atag (PrescribedRuntimeSpecialization.runtimeEnvironment (m+2))
   (CurrentRecursionBaseProgram.rawValues (baseTags J) target (counter ::ᵥ inputs))) =
 inputs.map (LiteralNumeralPrefix.numeralCall J.ntag) := by
 ext i
 simp only [params,List.Vector.get_map,List.Vector.get_ofFn,termValue,
  PrescribedRuntimeSpecialization.runtimeEnvironment,CurrentRecursionBaseProgram.rawValues,
  Fin.lastCases_castSucc,List.Vector.get_cons_succ,baseTags]

theorem counterValue {m ctx : Nat} (J : Tags) (target counter : Term ctx) (inputs : List.Vector (Term ctx) m) :
 termValue J.ctag J.atag (PrescribedRuntimeSpecialization.runtimeEnvironment (m+2))
  (CurrentRecursionBaseProgram.rawValues (baseTags J) target (counter ::ᵥ inputs)) (.var 0) =
 LiteralNumeralPrefix.numeralCall J.ntag counter := by
 change (CurrentRecursionBaseProgram.rawValues (baseTags J) target (counter ::ᵥ inputs)).get ((0 : Fin (m+1)).castSucc) = _
 simp only [CurrentRecursionBaseProgram.rawValues,List.Vector.get_ofFn,Fin.lastCases_castSucc,List.Vector.get_zero,baseTags]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.EncodingSupport
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.EncodingSupport
