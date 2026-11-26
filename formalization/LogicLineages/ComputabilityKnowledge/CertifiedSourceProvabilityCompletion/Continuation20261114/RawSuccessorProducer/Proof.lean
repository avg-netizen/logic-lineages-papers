module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccessorProducer.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccessorProducer.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

theorem internalGraph : Targets.InternalGraph := by
 intro n p old a x I ctx t m cert
 let args := t ::ᵥ m ::ᵥ cert ::ᵥ nil
 have ht := projection p [] args 0
 have hm := projection p [] args 1
 have hc := projection p [] args 2
 have hn := unary p [] args LiteralNumeralPrefix.numeralCode (.projection 1) m
  (LiteralNumeralPrefix.numeralCall I.numeralTag m) hm
  (copies p [] LiteralNumeralPrefix.numeralCode I.numeralTag I.hnumeral (m ::ᵥ nil))
 obtain ⟨h⟩ := RawMulNewestAdditionIteration.CombinatorProof.congruenceCompute p old a x
  I.toEvaluation.toCurrent.toComputation.toEvaluator args _ _ _ _ _ _ ht hn hc I.producerTag I.hproducer
 exact ⟨Hilbert.Local.finish h⟩

theorem internalEvaluation : Targets.InternalEvaluation := by
 intro n p old a x I ctx t m cert index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid I.validatorTag t
 let A := RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel t
  (LiteralNumeralPrefix.numeralCall I.numeralTag m) cert
 let G := [A,V]
 have ht : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
 have hin : Hilbert.Local T ctx G A := .hypothesis List.mem_cons_self
 obtain ⟨he⟩ := RawUnaryEvaluation.StatementChecks.exactSuccessor n p old a x I.toEvaluation ctx t m cert index fuel
 have hout := Hilbert.Local.mp (.mp (.base he) ht) hin
 obtain ⟨hg⟩ := internalGraph n p old a x I ctx t m cert
 let formula := RawEqualityComposition.eqRaw I.consTag I.appendTag (RawAdditionComputation.succRaw I.consTag t)
  (LiteralNumeralPrefix.numeralCall I.numeralTag (.succ m))
 have hcg := callCongruence (T := T) (G := G) I.qctag
  (index ::ᵥ fuel ::ᵥ .zero ::ᵥ .add formula formula ::ᵥ producerCall I.producerTag t m cert ::ᵥ nil)
  (index ::ᵥ fuel ::ᵥ .zero ::ᵥ .add formula formula ::ᵥ
   RawSuccCongruence.certificate I.mpTag I.replaceTag I.reflexivityTag I.consTag I.appendTag
    t (LiteralNumeralPrefix.numeralCall I.numeralTag m) cert ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .base (.logical (.reflexive _))
   | succ i => cases i using Fin.cases with
     | zero => exact .base (.logical (.reflexive _))
     | succ i => cases i using Fin.cases with
       | zero => exact .base (.logical (.reflexive _))
       | succ i => cases i using Fin.cases with
         | zero => exact .base (.logical (.reflexive _))
         | succ i => cases i using Fin.cases with
           | zero => exact .base hg
           | succ i => exact Fin.elim0 i)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (localTrans _ _ _ hcg hout)))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccessorProducer.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccessorProducer.Proof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccessorProducer.Proof.internalGraph
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccessorProducer.Proof.internalEvaluation
