module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryOrder.StepProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryOrder.SplitProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport SupportProof StepProof

private def template {ctx : Nat} (a : Term ctx) : Formula (ctx+1) :=
  split (liftTerm a) (.var 0)
private theorem templateAt {ctx : Nat} (a b : Term ctx) :
    GorbowStandardInstances.instantiate (template a) b = split a b := by
  simp only [GorbowStandardInstances.instantiate,template,substSplit,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem additiveSplit : Targets.AdditiveSplit := by
  intro T ctx a b
  let phi := template a
  have hu : Derivation T (upper a .zero) :=
    .mp (upperIntro a .zero a) (Support.equalitySymmetry _ _ (zeroLeft a))
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = template a from rfl,templateAt]
    exact .mp (.logical (.orRight _ _)) hu
  obtain ⟨hl⟩ := lowerSuccessor T (liftTerm a) (.var 0)
  obtain ⟨hr⟩ := upperSuccessor T (liftTerm a) (.var 0)
  have hl' : Derivation T (.imp (lower (liftTerm a) (.var 0))
      (split (liftTerm a) (.succ (.var 0)))) :=
    Hilbert.compose (.logical (.orLeft _ _)) hl
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    change Derivation T (.imp (split (liftTerm a) (.var 0))
      (GorbowStandardInduction.successorInstance (template a)))
    simp only [GorbowStandardInduction.successorInstance,template,substSplit,
      substitute,successorLift,Fin.cases_zero]
    exact .mp (.mp (.logical (.orElim _ _ _)) hl') hr
  have h := atTerm phi b (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  rw [show phi = template a from rfl,templateAt] at h
  exact ⟨h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryOrder.SplitProof
