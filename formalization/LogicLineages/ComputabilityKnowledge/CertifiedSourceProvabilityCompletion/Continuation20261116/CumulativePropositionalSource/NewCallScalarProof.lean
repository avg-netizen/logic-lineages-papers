module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ConstructorValidityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewUnaryProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewTransitivityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CallAlgebraTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCallScalarProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
theorem unary {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old arithmetic : Program 1) (x : Program 3)
 (I : JointInstallation p f lhs rhs t old arithmetic x)
 (G : List (Formula ctx)) (universal : Bool) (a b code index fuel : Term ctx)
 (ha : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag a))
 (hb : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag b))
 (hh : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (core I.currentK.coreTag index fuel (equalValue I.previous.current.ctag I.previous.current.atag a b) code)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (equalValue I.previous.current.ctag I.previous.current.atag
    (FixedFormulaSubstitution.unaryValue I.previous.current.ctag (if universal then 5 else 2) a)
    (FixedFormulaSubstitution.unaryValue I.previous.current.ctag (if universal then 5 else 2) b))
   (PrescribedRuntimeCallCongruence.unaryCertificate (tags I.previous)
    (if universal then .universalFunction (.var 0) else .succ (.var 0)) a b code))) := by
 have h := NewUnaryProof.exactUnaryCongruence arity k p f lhs rhs t old arithmetic x I
  1 0 PrescribedRuntimeEquality.boundEnvironment
  (if universal then .universalFunction (.var 0) else .succ (.var 0)) ctx G nil a b code index fuel
  (fun i => Fin.elim0 i) ⟨ha⟩ ⟨hb⟩ ⟨hh⟩
 cases universal <;> exact h
theorem left {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old arithmetic : Program 1) (x : Program 3)
 (I : JointInstallation p f lhs rhs t old arithmetic x)
 (G : List (Formula ctx)) (multiply : Bool) (a b c code index fuel : Term ctx)
 (ha : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag a))
 (hb : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag b))
 (hc : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag c))
 (hh : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (core I.currentK.coreTag index fuel (equalValue I.previous.current.ctag I.previous.current.atag a c) code)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (equalValue I.previous.current.ctag I.previous.current.atag
    (binaryValue (tags I.previous) multiply a b) (binaryValue (tags I.previous) multiply c b))
   (PrescribedRuntimeEquality.unaryCertificate (tags I.previous).mtag (tags I.previous).ctag (tags I.previous).atag (tags I.previous).constructorTag
    (tags I.previous).rctag (tags I.previous).reflexivityTag binaryEnvironment (binaryTerm multiply (.var 0) (.var 1))
    (b ::ᵥ nil) a c code))) := by
 have hin : ∀ i : Fin 1, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag ((b ::ᵥ nil).get i))) := by
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨hb⟩
  | succ j => exact Fin.elim0 j
 have h := NewUnaryProof.exactUnaryCongruence arity k p f lhs rhs t old arithmetic x I
  2 1 binaryEnvironment (binaryTerm multiply (.var 0) (.var 1)) ctx G (b ::ᵥ nil) a c code index fuel hin ⟨ha⟩ ⟨hc⟩ ⟨hh⟩
 cases multiply <;> exact h
theorem right {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old arithmetic : Program 1) (x : Program 3)
 (I : JointInstallation p f lhs rhs t old arithmetic x)
 (G : List (Formula ctx)) (multiply : Bool) (a b c code index fuel : Term ctx)
 (ha : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag a))
 (hb : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag b))
 (hc : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag c))
 (hh : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (core I.currentK.coreTag index fuel (equalValue I.previous.current.ctag I.previous.current.atag a c) code)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (equalValue I.previous.current.ctag I.previous.current.atag
    (binaryValue (tags I.previous) multiply b a) (binaryValue (tags I.previous) multiply b c))
   (PrescribedRuntimeEquality.unaryCertificate (tags I.previous).mtag (tags I.previous).ctag (tags I.previous).atag (tags I.previous).constructorTag
    (tags I.previous).rctag (tags I.previous).reflexivityTag binaryEnvironment (binaryTerm multiply (.var 1) (.var 0))
    (b ::ᵥ nil) a c code))) := by
 have hin : ∀ i : Fin 1, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag ((b ::ᵥ nil).get i))) := by
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨hb⟩
  | succ j => exact Fin.elim0 j
 have h := NewUnaryProof.exactUnaryCongruence arity k p f lhs rhs t old arithmetic x I
  2 1 binaryEnvironment (binaryTerm multiply (.var 1) (.var 0)) ctx G (b ::ᵥ nil) a c code index fuel hin ⟨ha⟩ ⟨hc⟩ ⟨hh⟩
 cases multiply <;> exact h
theorem binary {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old arithmetic : Program 1) (x : Program 3)
 (I : JointInstallation p f lhs rhs t old arithmetic x)
 (G : List (Formula ctx)) (multiply : Bool) (a b c d hac hbd index fuel : Term ctx)
 (ha : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag a))
 (hb : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag b))
 (hc : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag c))
 (hd : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag d))
 (hhac : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (core I.currentK.coreTag index fuel (equalValue I.previous.current.ctag I.previous.current.atag a c) hac))
 (hhbd : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (core I.currentK.coreTag index fuel (equalValue I.previous.current.ctag I.previous.current.atag b d) hbd)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (equalValue I.previous.current.ctag I.previous.current.atag (binaryValue (tags I.previous) multiply a b) (binaryValue (tags I.previous) multiply c d))
   (binaryCertificate (tags I.previous) multiply a b c d hac hbd))) := by
 obtain ⟨hp⟩ := left p f lhs rhs t old arithmetic x I G multiply a b c hac index fuel ha hb hc hhac
 obtain ⟨hq⟩ := right p f lhs rhs t old arithmetic x I G multiply b c d hbd index fuel hb hc hd hhbd
 have hpc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hp
 have hqc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hq
 obtain ⟨hab⟩ := ConstructorValidityProof.binary p f lhs rhs t old arithmetic x I.previous G multiply a b ha hb
 obtain ⟨hcb⟩ := ConstructorValidityProof.binary p f lhs rhs t old arithmetic x I.previous G multiply c b hc hb
 obtain ⟨hcd⟩ := ConstructorValidityProof.binary p f lhs rhs t old arithmetic x I.previous G multiply c d hc hd
 exact NewTransitivityProof.exactTransitivity arity k p f lhs rhs t old arithmetic x I ctx G
  (binaryValue (tags I.previous) multiply a b) (binaryValue (tags I.previous) multiply c b) (binaryValue (tags I.previous) multiply c d)
  _ _ index fuel ⟨hab⟩ ⟨hcb⟩ ⟨hcd⟩ ⟨hpc⟩ ⟨hqc⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCallScalarProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCallScalarProof
