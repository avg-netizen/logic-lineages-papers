module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.TruthSupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.TruthValidity
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open TruthSupport
theorem valid {n k ctx : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old ar : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old ar x)
 (G : List (Formula ctx)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (UniformClosedPropositional.formulaValid I.currentK.fval (truthCode : Term ctx))) := by
 obtain ⟨hz⟩ := TruthSupport.zeroValid p f lhs rhs t old ar x I G
 obtain ⟨hv⟩ := CurrentEqualityImplication.GuardProof.equal p f lhs rhs t old ar x I G false zeroCode zeroCode hz hz
 obtain ⟨he⟩ := TruthSupport.equation (ctx := ctx) p f lhs rhs t old ar x I
 have hcall := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) I.currentK.fval
  ((.zero : Term ctx) ::ᵥ equalValue I.previous.current.ctag I.previous.current.atag zeroCode zeroCode ::ᵥ nil)
  (.zero ::ᵥ truthCode ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .logical (.reflexive _)
   | succ i => cases i using Fin.cases with
     | zero => exact he
     | succ i => exact Fin.elim0 i)
 exact ⟨localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hcall)) hv⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.TruthValidity
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.TruthValidity
