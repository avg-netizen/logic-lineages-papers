module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionEvaluation.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionEvaluation.CongruenceProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof
open SixSol20261112.Fuel NamedArithmeticGraph

theorem internalCongruence : Targets.InternalCongruence := by
 intro n p old a x I ctx t t' u u' first second index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid I.validatorTag t
 let W := RawReflexivityDispatcher.valid I.validatorTag t'
 let U := RawReflexivityDispatcher.valid I.validatorTag u
 let Z := RawReflexivityDispatcher.valid I.validatorTag u'
 let A := RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel t t' first
 let B := RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel u u' second
 let G := [B,A,Z,U,W,V]
 have ht : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
 have ht' : Hilbert.Local T ctx G W := .hypothesis (by simp [G])
 have hu : Hilbert.Local T ctx G U := .hypothesis (by simp [G])
 have hu' : Hilbert.Local T ctx G Z := .hypothesis (by simp [G])
 have hf : Hilbert.Local T ctx G A := .hypothesis (by simp [G])
 have hs : Hilbert.Local T ctx G B := .hypothesis List.mem_cons_self
 obtain ⟨hl⟩ := RawMulNewestAddCongruences.StatementChecks.exactRight n p old a x I ctx t t' u first index fuel
 have hleft := Hilbert.Local.mp (.mp (.mp (.mp (.base hl) ht) ht') hu) hf
 obtain ⟨hr⟩ := RawMulNewestAddCongruences.StatementChecks.exactLeft n p old a x I ctx u u' t' second index fuel
 have hright := Hilbert.Local.mp (.mp (.mp (.mp (.base hr) hu) hu') ht') hs
 have addValid (s z : Term ctx)
  (hS : Hilbert.Local T ctx G (RawReflexivityDispatcher.valid I.validatorTag s))
  (hZ : Hilbert.Local T ctx G (RawReflexivityDispatcher.valid I.validatorTag z)) :
  Hilbert.Local T ctx G (RawReflexivityDispatcher.valid I.validatorTag
   (RawAddRightCongruence.addRaw I.consTag I.appendTag s z)) := by
  apply Classical.choice
  obtain ⟨h⟩ := RawAdditionComputation.ValidityProof.internalAdditionValidity n p I.validatorTag I.pairTag I.consTag I.appendTag
   I.hv I.hp I.hc I.ha ctx s z
  exact ⟨.mp (.mp (.base h) hS) hZ⟩
 obtain ⟨htrans⟩ := RawMulNewestTransitivity.StatementChecks.exactTransitivity n p old (RawMulNewestAddition.arithmetic a) x I.toCurrent.toComputation.toEvaluator.toAddition.toCongruence.toNewestEquality ctx
  (RawAddRightCongruence.addRaw I.consTag I.appendTag t u)
  (RawAddRightCongruence.addRaw I.consTag I.appendTag t' u)
  (RawAddRightCongruence.addRaw I.consTag I.appendTag t' u')
  (RawAddRightCongruence.certificate I.mpTag I.addRightLineTag I.reflexivityTag I.consTag I.appendTag t t' u first)
  (RawAddLeftCongruence.certificate I.mpTag I.addLeftLineTag I.reflexivityTag I.consTag I.appendTag u u' t' second) index fuel
 have hout := Hilbert.Local.mp (.mp (.mp (.mp (.mp (.base htrans)
  (addValid t u ht hu)) (addValid t' u ht' hu)) (addValid t' u' ht' hu')) hleft) hright
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
  (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge hout))))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionEvaluation.CongruenceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionEvaluation.CongruenceProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionEvaluation.CongruenceProof.internalCongruence
