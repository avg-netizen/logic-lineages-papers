module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.Preflight
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.GuardProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedTemplateEncodingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.ClosedValidity
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem formula {n k ctx : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old ar : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old ar x)
 (G : List (Formula ctx)) (a : Formula 0) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (UniformClosedPropositional.formulaValid I.currentK.fval (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode a))))) := by
 let e := FullFormulaInstantiationValidity.FixedTemplateEncodingTargets.boundEnvironment 0
 obtain ⟨hv⟩ := CurrentEqualityImplication.GuardProof.formula p f lhs rhs t old ar x I G false e a nil (fun i => Fin.elim0 i)
 obtain ⟨he⟩ := FullFormulaInstantiationValidity.FixedTemplateEncodingProof.boundFormulaEncoding 0 a n p
  I.previous.current.ctag I.previous.current.atag I.previous.current.h_ctag I.previous.current.h_atag ctx
 have hcall := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) I.currentK.fval
  ((.zero : Term ctx) ::ᵥ FixedFormulaSubstitution.formulaValue I.previous.current.ctag I.previous.current.atag nil a e ::ᵥ nil)
  (.zero ::ᵥ Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode a)) ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .logical (.reflexive _)
   | succ i => cases i using Fin.cases with
    | zero => exact he
    | succ i => exact Fin.elim0 i)
 exact ⟨localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hcall)) hv⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.ClosedValidity
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.ClosedValidity
