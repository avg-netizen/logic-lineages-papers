module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationEvaluation.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationEvaluation.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph

theorem internalEvaluation : Targets.InternalEvaluation := by
 intro n p old a x I ctx t u m k first second index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let nm := LiteralNumeralPrefix.numeralCall I.numeralTag m
 let nk := LiteralNumeralPrefix.numeralCall I.numeralTag k
 let ns := LiteralNumeralPrefix.numeralCall I.numeralTag (.mul m k)
 let V := RawReflexivityDispatcher.valid I.validatorTag t
 let W := RawReflexivityDispatcher.valid I.validatorTag u
 let A := RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel t nm first
 let B := RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel u nk second
 let G := [B,A,W,V]
 have ht : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
 have hu : Hilbert.Local T ctx G W := .hypothesis (by simp [G])
 have hf : Hilbert.Local T ctx G A := .hypothesis (by simp [G])
 have hs : Hilbert.Local T ctx G B := .hypothesis List.mem_cons_self
 obtain ⟨hvm⟩ := RawMulNewestAdditionIteration.InvariantSupport.numeralValid p old a x I.toComputation.toEvaluator m
 obtain ⟨hvk⟩ := RawMulNewestAdditionIteration.InvariantSupport.numeralValid p old a x I.toComputation.toEvaluator k
 obtain ⟨hvsum⟩ := RawMulNewestAdditionIteration.InvariantSupport.numeralValid p old a x I.toComputation.toEvaluator (.mul m k)
 obtain ⟨hcong⟩ := RawBinaryMultiplicationCongruence.StatementChecks.exactCongruence n p old (RawMulNewestAddition.arithmetic a) x
  I.toComputation.toEvaluator.toAddition.toCongruence.toNewestEquality ctx t nm u nk first second index fuel
 have hc := Hilbert.Local.mp (.mp (.mp (.mp (.mp (.mp (.base hcong) ht) (.base hvm)) hu) (.base hvk)) hf) hs
 obtain ⟨hiteration⟩ := RawNewestMultiplicationIteration.StatementChecks.exactIteration n p old a x I ctx m k index fuel
 have hsum := GorbowTheoryProof.Derivation.mp (.logical (.andRight _ _))
  (GorbowTheoryProof.Derivation.mp (.logical (.andRight _ _)) hiteration)
 obtain ⟨hvtu⟩ := RawMultiplicationComputation.ValidityProof.internalMultiplicationValidity n p I.validatorTag I.pairTag I.consTag I.appendTag
  I.hv I.hp I.hc I.ha ctx t u
 have vtu := Hilbert.Local.mp (.mp (.base hvtu) ht) hu
 obtain ⟨hvmk⟩ := RawMultiplicationComputation.ValidityProof.internalMultiplicationValidity n p I.validatorTag I.pairTag I.consTag I.appendTag
  I.hv I.hp I.hc I.ha ctx nm nk
 have vmk : Hilbert.Local T ctx G _ := .mp (.mp (.base hvmk) (.base hvm)) (.base hvk)
 obtain ⟨htrans⟩ := RawMulNewestTransitivity.StatementChecks.exactTransitivity n p old (RawMulNewestAddition.arithmetic a) x
  I.toComputation.toEvaluator.toAddition.toCongruence.toNewestEquality ctx
  (RawNewestMultiplicationComputation.mulRaw I.consTag I.appendTag t u)
  (RawNewestMultiplicationComputation.mulRaw I.consTag I.appendTag nm nk) ns
  (RawBinaryMultiplicationCongruence.certificate I.mpTag I.qtag I.rightLineTag I.equalityLineTag I.reflexivityTag I.consTag I.appendTag
   t nm u nk first second)
  (RawIteratedSucc.third I.rightTag (RawAdditionIteration.binaryCall I.mulIteratorTag k m)) index fuel
 have hout := Hilbert.Local.mp (.mp (.mp (.mp (.mp (.base htrans) vtu) vmk) (.base hvsum)) hc) (.base hsum)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
  (Hilbert.Local.discharge (Hilbert.Local.discharge hout))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationEvaluation.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationEvaluation.Proof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationEvaluation.Proof.internalEvaluation
