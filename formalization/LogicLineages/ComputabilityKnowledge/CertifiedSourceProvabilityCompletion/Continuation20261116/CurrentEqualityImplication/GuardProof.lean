module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.GuardProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem formula {arity k ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x)
 (G : List (Formula ctx)) (isS : Bool) {n inputs : Nat}
 (e : FixedFormulaSubstitution.Environment n 0 inputs) (f : Formula n)
 (raw : List.Vector (Term ctx) inputs)
 (hraw : ∀ i, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag (raw.get i)))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (UniformClosedPropositional.formulaValid
   (RebaseProof.selected p installed lhs rhs t old a x I isS).fval
   (FixedFormulaSubstitution.formulaValue I.previous.current.ctag I.previous.current.atag raw f e))) := by
 let J := I.previous.current
 let K := RebaseProof.selected p installed lhs rhs t old a x I isS
 obtain ⟨hs⟩ := FullFormulaInstantiationValidity.FixedFormulaValidityProof.fixedFormulaValidity n 0 inputs e f
  arity p J.vtag J.stag J.ptag J.ctag J.atag J.h_vtag J.h_stag J.h_ptag J.h_ctag J.h_atag ctx G raw hraw
 obtain ⟨_,_,_,etag,_,_,_,he⟩ := LiteralSyntaxValidator.FormulaBindingProof.nodesInstalled p K.fval K.h_fval
 obtain ⟨hc⟩ := LiteralSyntaxValidator.FormulaBindingProof.complete p K.fval J.stag J.ptag J.ctag etag
  K.h_fval J.h_stag J.h_ptag J.h_ctag he (.zero : Term ctx)
  (FixedFormulaSubstitution.formulaValue J.ctag J.atag raw f e)
 exact ⟨.mp (.base hc) hs⟩

theorem equal {arity k ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x)
 (G : List (Formula ctx)) (isS : Bool) (left right : Term ctx)
 (hl : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag left))
 (hr : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag right)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (UniformClosedPropositional.formulaValid (RebaseProof.selected p installed lhs rhs t old a x I isS).fval
   (equalValue I.previous.current.ctag I.previous.current.atag left right))) := by
 let e : FixedFormulaSubstitution.Environment 2 0 2 := fun i => .inr i
 have hin : ∀ i : Fin 2, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag ((left ::ᵥ right ::ᵥ nil).get i))) := by
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨hl⟩
  | succ i => cases i using Fin.cases with
    | zero => exact ⟨hr⟩
    | succ i => exact Fin.elim0 i
 exact formula p installed lhs rhs t old a x I G isS e (.equal (.var 0) (.var 1)) (left ::ᵥ right ::ᵥ nil) hin

theorem implication {arity k ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x)
 (G : List (Formula ctx)) (isS : Bool) (A B : Term ctx)
 (hA : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (UniformClosedPropositional.formulaValid (RebaseProof.selected p installed lhs rhs t old a x I isS).fval A))
 (hB : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (UniformClosedPropositional.formulaValid (RebaseProof.selected p installed lhs rhs t old a x I isS).fval B)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (UniformClosedPropositional.formulaValid (RebaseProof.selected p installed lhs rhs t old a x I isS).fval
   (impValue I.previous.current.ctag I.previous.current.atag A B))) :=
 UniformClosedPropositionalCertificate.ImplicationValidityProof.implication p _ _ _ isS
  (RebaseProof.rebase p installed lhs rhs t old a x I isS) G A B hA hB

theorem copy {arity k ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x)
 (G : List (Formula ctx)) (isS : Bool) (P : Term ctx)
 (hP : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (UniformClosedPropositional.formulaValid I.currentK.fval P)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (UniformClosedPropositional.formulaValid (RebaseProof.selected p installed lhs rhs t old a x I isS).fval P)) := by
 obtain ⟨he⟩ := GorbowPRInternalCoherence.Proof.registryCoherence arity p
  (RebaseProof.selected p installed lhs rhs t old a x I isS).fval I.currentK.fval 2 LiteralSyntaxValidator.formulaValidator
  (RebaseProof.selected p installed lhs rhs t old a x I isS).h_fval I.currentK.h_fval ctx (.zero ::ᵥ P ::ᵥ nil)
 exact ⟨localTrans _ _ _ (.base he) hP⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.GuardProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.GuardProof
