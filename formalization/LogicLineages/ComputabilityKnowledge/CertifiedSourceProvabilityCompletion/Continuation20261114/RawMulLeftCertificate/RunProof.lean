module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftCertificate.EntryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftCertificate.RunProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix TwoSol20261113.ReflexivityCertificate
open SixSol20261112.Fuel SixSol20261112.HistoryMachine NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryRunSplice HistoryKernel.TransitionEquationsProof

theorem internalSingletonRun : Targets.InternalSingletonRun := by
 intro n p old arithmetic x I ctx raw rawB rawV index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid I.validatorTag raw
 let K := RawReflexivityDispatcher.valid I.validatorTag rawB
 let L := RawReflexivityDispatcher.valid I.validatorTag rawV
 let G := [L,K,H]
 have hh : Hilbert.Local T ctx G H := .hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
 have hkValid : Hilbert.Local T ctx G K := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hlValid : Hilbert.Local T ctx G L := .hypothesis List.mem_cons_self
 let qline := RawMulLeftReplace.lineCall I.qtag raw rawB rawV
 let cert := RawMulLeftCertificate.certificate I.consTag I.qtag raw rawB rawV
 let kt := I.itag+stepTag iterationBase+1
 let count := call (I.consTag+GorbowPRChildTags.argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0)
  (qline ::ᵥ .zero ::ᵥ nil)
 have hk := IdleProof.kernelInstalled p I.itag LiteralSyntaxValidator.lineValidator (RawMulLeftReplace.logicalLeaf old) arithmetic x I.hi
 obtain ⟨_,_,_,hdisp,_⟩ := HistoryKernel.OptionProof.kernelNodes p kt LiteralSyntaxValidator.lineValidator (RawMulLeftReplace.logicalLeaf old) arithmetic x hk
 obtain ⟨haccept⟩ := RawMulLeftDispatcher.StatementChecks.exactDispatcher n p old arithmetic x
  I.toDispatcher ctx raw rawB rawV index fuel .zero
 obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p
  (dispatcherTag kt LiteralSyntaxValidator.lineValidator (RawMulLeftReplace.logicalLeaf old) arithmetic x) I.dtag 4
  (RawMulLeftDispatcher.dispatcher old arithmetic x) hdisp I.hdispatcher ctx (index ::ᵥ fuel ::ᵥ .zero ::ᵥ qline ::ᵥ nil)
 obtain ⟨hoption⟩ := HistoryKernel.OptionProof.optionAccepted p kt LiteralSyntaxValidator.lineValidator (RawMulLeftReplace.logicalLeaf old) arithmetic x hk index fuel .zero qline
 have ho := Hilbert.Local.mp (.base hoption)
  (localTrans _ _ _ (.base hcopy) (.mp (.mp (.mp (.base haccept) hh) hkValid) hlValid))
 obtain ⟨hentry⟩ := EntryProof.rawNewHistory p old arithmetic x I raw rawB rawV
  (someTag kt LiteralSyntaxValidator.lineValidator (RawMulLeftReplace.logicalLeaf old) arithmetic x) (someInstalled p kt LiteralSyntaxValidator.lineValidator (RawMulLeftReplace.logicalLeaf old) arithmetic x hk)
 have hs := Logic.unary (.succ (.var 0)) _ _ hentry
 have hout := localTrans _ _ _ ho (.base hs)
 obtain ⟨hcons⟩ := HistoryCodec.PairProof.internalCons n p I.consTag I.hc ctx qline .zero
 obtain ⟨hstep⟩ := ConsRunProof.someCons p I.itag I.pairTag I.consTag LiteralSyntaxValidator.lineValidator (RawMulLeftReplace.logicalLeaf old) arithmetic x
  I.hi I.hp I.hc count .zero qline .zero index fuel
 obtain ⟨hidle⟩ := IdleProof.internalIdle LiteralSyntaxValidator.lineValidator (RawMulLeftReplace.logicalLeaf old) arithmetic x n p I.itag I.pairTag I.hi I.hp ctx count
  (optionValue kt LiteralSyntaxValidator.lineValidator (RawMulLeftReplace.logicalLeaf old) arithmetic x index fuel .zero qline) index fuel
 have hcount := StationaryProof.iterationCount (T := T) (G := G) I.itag cert (.succ count)
  (state I.pairTag (.succ .zero) cert) index fuel (.base hcons)
 have hpair := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := G) I.pairTag _ .zero _ .zero
  hout (.base (.logical (.reflexive .zero)))
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge (localTrans _ _ _ hcount
  (localTrans _ _ _ (.base hstep) (localTrans _ _ _ (.base hidle) hpair))))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftCertificate.RunProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftCertificate.RunProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftCertificate.RunProof.internalSingletonRun
