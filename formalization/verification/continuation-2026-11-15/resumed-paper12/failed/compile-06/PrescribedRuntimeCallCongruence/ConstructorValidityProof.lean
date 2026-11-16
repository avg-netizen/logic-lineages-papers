module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ValidityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ConstructorValidityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
theorem unary {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old arithmetic : Program 1) (x : Program 3)
 (I : CumulativeUniformRule12Registry.JointInstallation p f lhs rhs t old arithmetic x)
 (G : List (Formula ctx)) (universal : Bool) (raw : Term ctx)
 (hr : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.current.vtag raw)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.current.vtag
   (FixedFormulaSubstitution.unaryValue I.current.ctag (if universal then 5 else 2) raw))) := by
 let e : FixedFormulaSubstitution.Environment 1 0 1 := fun i => .inr i
 have hin : ∀ i : Fin 1, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.current.vtag ((raw ::ᵥ nil).get i))) := by
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨hr⟩
  | succ j => exact Fin.elim0 j
 cases universal with
 | false => exact ValidityProof.term p _ _ _ I.current e (.succ (.var 0)) G (raw ::ᵥ nil) hin
 | true => exact ValidityProof.term p _ _ _ I.current e (.universalFunction (.var 0)) G (raw ::ᵥ nil) hin
theorem binary {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old arithmetic : Program 1) (x : Program 3)
 (I : CumulativeUniformRule12Registry.JointInstallation p f lhs rhs t old arithmetic x)
 (G : List (Formula ctx)) (multiply : Bool) (a b : Term ctx)
 (ha : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.current.vtag a))
 (hb : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.current.vtag b)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.current.vtag (binaryValue (tags I) multiply a b))) := by
 let e : FixedFormulaSubstitution.Environment 2 0 2 := fun i => .inr i
 have hin : ∀ i : Fin 2, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.current.vtag ((a ::ᵥ b ::ᵥ nil).get i))) := by
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨ha⟩
  | succ j => cases j using Fin.cases with
    | zero => exact ⟨hb⟩
    | succ j => exact Fin.elim0 j
 cases multiply with
 | false => exact ValidityProof.term p _ _ _ I.current e (.add (.var 0) (.var 1)) G (a ::ᵥ b ::ᵥ nil) hin
 | true => exact ValidityProof.term p _ _ _ I.current e (.mul (.var 0) (.var 1)) G (a ::ᵥ b ::ᵥ nil) hin
theorem pair {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old arithmetic : Program 1) (x : Program 3)
 (I : CumulativeUniformRule12Registry.JointInstallation p f lhs rhs t old arithmetic x)
 (G : List (Formula ctx)) (a b : Term ctx)
 (ha : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.current.vtag a))
 (hb : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.current.vtag b)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.current.vtag (pairValue (tags I) a b))) := by
 obtain ⟨hs⟩ := binary p f lhs rhs t old arithmetic x I G false a b ha hb
 obtain ⟨hm⟩ := binary p f lhs rhs t old arithmetic x I G true
  (binaryValue (tags I) false a b) (binaryValue (tags I) false a b) hs hs
 exact binary p f lhs rhs t old arithmetic x I G false _ a hm ha
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ConstructorValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ConstructorValidityProof
