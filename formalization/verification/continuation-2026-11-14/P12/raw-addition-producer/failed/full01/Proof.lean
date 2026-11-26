module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionProducer.GraphProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionProducer.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
theorem internalEvaluation : Targets.InternalEvaluation := by
 intro n p old a x I ctx t u m k first second index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid I.validatorTag t
 let W := RawReflexivityDispatcher.valid I.validatorTag u
 let A := RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel t
  (LiteralNumeralPrefix.numeralCall I.numeralTag m) first
 let B := RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel u
  (LiteralNumeralPrefix.numeralCall I.numeralTag k) second
 let G := [B,A,W,V]
 have ht : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
 have hu : Hilbert.Local T ctx G W := .hypothesis (by simp [G])
 have hin : Hilbert.Local T ctx G A := .hypothesis (by simp [G])
 have hsecond : Hilbert.Local T ctx G B := .hypothesis List.mem_cons_self
 obtain ⟨he⟩ := RawMulNewestAdditionEvaluation.StatementChecks.exactEvaluation n p old a x I.toEvaluation ctx t u m k first second index fuel
 have hout := Hilbert.Local.mp (.mp (.mp (.mp (.base he) ht) hu) hin) hsecond
 obtain ⟨hg⟩ := GraphProof.internalGraph n p old a x I ctx t u m k first second
 let formula := RawEqualityComposition.eqRaw I.consTag I.appendTag (RawAdditionComputation.addRaw I.consTag I.appendTag t u)
  (LiteralNumeralPrefix.numeralCall I.numeralTag (.add m k))
 have hcg := callCongruence (T := T) (G := G) I.qctag
  (index ::ᵥ fuel ::ᵥ .zero ::ᵥ .add formula formula ::ᵥ producerCall I.producerTag t u m k first second ::ᵥ nil)
  (index ::ᵥ fuel ::ᵥ .zero ::ᵥ .add formula formula ::ᵥ
   RawMulNewestAdditionEvaluation.certificate I.mpTag I.addLeftLineTag I.addRightLineTag I.equalityLineTag I.reflexivityTag
    I.consTag I.appendTag I.numeralTag I.iteratorTag I.rightTag t u m k first second ::ᵥ nil) (fun i => by
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
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge (localTrans _ _ _ hcg hout)))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionProducer.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionProducer.Proof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionProducer.Proof.internalEvaluation
