module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.SymbolicProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence CurrentImplicationCertificate CurrentEqualityImplication
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open FixedFormulaSubstitution GorbowPRDefiningEquations

theorem rootMember {arity m : Nat} (p : Program arity) (f : Program m) (g : Program (m+2)) (tag : Nat)
 (h : (nodes p)[tag]? = some ⟨m+1,Program.recursion f g⟩) :
 GorbowStandardInduction.universalClosure (rootFormula f tag) ∈ axioms p := by
 apply EffectiveNumeral.NodeSupport.intoRegistry (.recursion f g) arity p tag h
 apply EffectiveNumeral.NodeSupport.rootIncluded
 exact List.mem_cons_of_mem _ List.mem_cons_self

theorem runtimeTail {m ctx : Nat} (ctag atag : Nat) (counter : Term ctx) (raw : List.Vector (Term ctx) m) :
 (tailVariables m).map (termValue ctag atag (PrescribedRuntimeSpecialization.runtimeEnvironment (m+1)) (counter ::ᵥ raw)) = raw := by
 apply List.Vector.ext
 intro i
 simp only [tailVariables,List.Vector.get_map,List.Vector.get_ofFn,termValue,
  PrescribedRuntimeSpecialization.runtimeEnvironment,List.Vector.get_cons_succ]

theorem stepArgs {m ctx : Nat} (ctag atag : Nat) (counter replacement : Term ctx)
 (raw : List.Vector (Term ctx) m) :
 (.var 1 ::ᵥ .var 0 ::ᵥ List.Vector.ofFn (fun i : Fin m => (.var i.succ.succ : Term (m+2)))).map
  (termValue ctag atag (UniformRuntimeEnvironmentAgreement.specialize (stepEnvironment m))
   (replacement ::ᵥ counter ::ᵥ raw)) = counter ::ᵥ replacement ::ᵥ raw := by
 apply List.Vector.ext
 intro i
 cases i using Fin.cases with
 | zero => rfl
 | succ i => cases i using Fin.cases with
   | zero => rfl
   | succ i => simp only [List.Vector.get_map,List.Vector.get_cons_succ,List.Vector.get_ofFn,
      termValue,UniformRuntimeEnvironmentAgreement.specialize,stepEnvironment,Fin.cases_succ,List.Vector.get_cons_succ]

theorem stepValue {arity m ctx : Nat} (p : Program arity) (J : PrescribedRuntimeCallCongruence.Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hn : (nodes p)[J.numeralTag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (tag : Nat) (counter replacement : Term ctx) (raw : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (specializedValue J.ctag J.atag (stepEnvironment m) (stepTemplate m tag)
   (counter ::ᵥ raw) replacement)
   (callValue J (Term.numeral tag) (counter ::ᵥ replacement ::ᵥ raw)))) := by
 obtain ⟨h⟩ := CurrentCompositionCertificate.CallEncodingProof.call p J hc ha hn
  (UniformRuntimeEnvironmentAgreement.specialize (stepEnvironment m)) (replacement ::ᵥ counter ::ᵥ raw) tag
  (.var 1 ::ᵥ .var 0 ::ᵥ List.Vector.ofFn (fun i : Fin m => .var i.succ.succ))
 rw [stepArgs] at h
 exact ⟨h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.SymbolicProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.SymbolicProof
