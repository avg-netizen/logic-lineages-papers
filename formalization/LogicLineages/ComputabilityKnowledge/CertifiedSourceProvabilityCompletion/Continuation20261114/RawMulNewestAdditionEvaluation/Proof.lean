module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionEvaluation.CongruenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionEvaluation.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph

theorem internalEvaluation : Targets.InternalEvaluation := by
 intro n p old a x I ctx t u m k first second index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let nm := LiteralNumeralPrefix.numeralCall I.numeralTag m
 let nk := LiteralNumeralPrefix.numeralCall I.numeralTag k
 let ns := LiteralNumeralPrefix.numeralCall I.numeralTag (.add m k)
 let V := RawReflexivityDispatcher.valid I.validatorTag t
 let W := RawReflexivityDispatcher.valid I.validatorTag u
 let A := RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel t nm first
 let B := RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel u nk second
 let G := [B,A,W,V]
 have ht : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
 have hu : Hilbert.Local T ctx G W := .hypothesis (by simp [G])
 have hf : Hilbert.Local T ctx G A := .hypothesis (by simp [G])
 have hs : Hilbert.Local T ctx G B := .hypothesis List.mem_cons_self
 obtain ⟨hvm⟩ := RawMulNewestAdditionIteration.InvariantSupport.numeralValid p old a x I.toCurrent.toComputation.toEvaluator m
 obtain ⟨hvk⟩ := RawMulNewestAdditionIteration.InvariantSupport.numeralValid p old a x I.toCurrent.toComputation.toEvaluator k
 obtain ⟨hvsum⟩ := RawMulNewestAdditionIteration.InvariantSupport.numeralValid p old a x I.toCurrent.toComputation.toEvaluator (.add m k)
 obtain ⟨hcong⟩ := CongruenceProof.internalCongruence n p old a x I ctx t nm u nk first second index fuel
 have hc := Hilbert.Local.mp (.mp (.mp (.mp (.mp (.mp (.base hcong) ht) (.base hvm)) hu) (.base hvk)) hf) hs
 obtain ⟨hsum⟩ := RawMulNewestAdditionIteration.StatementChecks.exactNumeralAddition n p old a x I.toCurrent.toComputation.toEvaluator ctx m k index fuel
 obtain ⟨hvtu⟩ := RawAdditionComputation.ValidityProof.internalAdditionValidity n p I.validatorTag I.pairTag I.consTag I.appendTag
  I.hv I.hp I.hc I.ha ctx t u
 have vtu := Hilbert.Local.mp (.mp (.base hvtu) ht) hu
 obtain ⟨hvmk⟩ := RawAdditionComputation.ValidityProof.internalAdditionValidity n p I.validatorTag I.pairTag I.consTag I.appendTag
  I.hv I.hp I.hc I.ha ctx nm nk
 have vmk : Hilbert.Local T ctx G _ := .mp (.mp (.base hvmk) (.base hvm)) (.base hvk)
 obtain ⟨htrans⟩ := RawMulNewestTransitivity.StatementChecks.exactTransitivity n p old (RawMulNewestAddition.arithmetic a) x
  I.toCurrent.toComputation.toEvaluator.toAddition.toCongruence.toNewestEquality ctx
  (RawAdditionComputation.addRaw I.consTag I.appendTag t u)
  (RawAdditionComputation.addRaw I.consTag I.appendTag nm nk) ns
  (RawBinaryAdditionCongruence.certificate I.mpTag I.addLeftLineTag I.addRightLineTag I.equalityLineTag I.reflexivityTag I.consTag I.appendTag
   t nm u nk first second)
  (RawIteratedSucc.third I.rightTag (RawNewestAdditionIteration.binaryCall I.iteratorTag k nm)) index fuel
 have hout := Hilbert.Local.mp (.mp (.mp (.mp (.mp (.base htrans) vtu) vmk) (.base hvsum)) hc) (.base hsum)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
  (Hilbert.Local.discharge (Hilbert.Local.discharge hout))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionEvaluation.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionEvaluation.Proof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionEvaluation.Proof.internalEvaluation
