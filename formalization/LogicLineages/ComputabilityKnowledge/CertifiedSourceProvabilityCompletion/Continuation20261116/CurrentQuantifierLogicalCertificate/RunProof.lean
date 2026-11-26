module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.EntryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.RunProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix TwoSol20261113.ReflexivityCertificate
open SixSol20261112.Fuel SixSol20261112.HistoryMachine NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryRunSplice HistoryKernel.TransitionEquationsProof

theorem internalRawSingletonRun {n ctx : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (rawOld arithmetic : Program 1) (x : Program 3)
 (isS : Bool) (I : Installation p f lhs rhs rawOld arithmetic x isS) (formula leftTerm index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (OriginalQuantifierLogicalExtension.guards isS I.fval formula leftTerm)
   (.equal (LiteralCheckerAcceptance.runCall I.iteratorTag I.ptag index fuel
    (rawCertificate I.ctag I.quantifierTag formula leftTerm))
    (output isS I.ptag I.ctag I.atag formula leftTerm)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := OriginalQuantifierLogicalExtension.guards isS I.fval formula leftTerm
 let G := [H]
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 let qline := OriginalQuantifierLogicalProducers.lineCall I.quantifierTag formula leftTerm
 let cert := CurrentQuantifierLogicalCertificate.rawCertificate I.ctag I.quantifierTag formula leftTerm
 let kt := I.iteratorTag+stepTag iterationBase+1
 let count := call (I.ctag+GorbowPRChildTags.argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0)
  (qline ::ᵥ .zero ::ᵥ nil)
 have hk := IdleProof.kernelInstalled p I.iteratorTag LiteralSyntaxValidator.lineValidator (logical f lhs rhs rawOld) arithmetic x I.h_iteratorTag
 obtain ⟨_,_,_,hdisp,_⟩ := HistoryKernel.OptionProof.kernelNodes p kt LiteralSyntaxValidator.lineValidator (logical f lhs rhs rawOld) arithmetic x hk
 obtain ⟨haccept⟩ := DispatcherProof.internalDispatcher p f lhs rhs rawOld arithmetic x isS I formula leftTerm index fuel .zero
 obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p
  (dispatcherTag kt LiteralSyntaxValidator.lineValidator (logical f lhs rhs rawOld) arithmetic x) I.dispatcherTag 4
  (CurrentQuantifierLogicalCertificate.dispatcher f lhs rhs rawOld arithmetic x) hdisp I.h_dispatcherTag ctx (index ::ᵥ fuel ::ᵥ .zero ::ᵥ qline ::ᵥ nil)
 obtain ⟨hoption⟩ := HistoryKernel.OptionProof.optionAccepted p kt LiteralSyntaxValidator.lineValidator (logical f lhs rhs rawOld) arithmetic x hk index fuel .zero qline
 have ho := Hilbert.Local.mp (.base hoption)
  (localTrans _ _ _ (.base hcopy) (.mp (.base haccept) hh))
 obtain ⟨hentry⟩ := EntryProof.rawNewHistory p f lhs rhs rawOld arithmetic x isS I formula leftTerm
  (someTag kt LiteralSyntaxValidator.lineValidator (logical f lhs rhs rawOld) arithmetic x) (someInstalled p kt LiteralSyntaxValidator.lineValidator (logical f lhs rhs rawOld) arithmetic x hk)
 have hs := Logic.unary (.succ (.var 0)) _ _ hentry
 have hout := localTrans _ _ _ ho (.base hs)
 obtain ⟨hcons⟩ := HistoryCodec.PairProof.internalCons n p I.ctag I.h_ctag ctx qline .zero
 obtain ⟨hstep⟩ := ConsRunProof.someCons p I.iteratorTag I.ptag I.ctag LiteralSyntaxValidator.lineValidator (logical f lhs rhs rawOld) arithmetic x
  I.h_iteratorTag I.h_ptag I.h_ctag count .zero qline .zero index fuel
 obtain ⟨hidle⟩ := IdleProof.internalIdle LiteralSyntaxValidator.lineValidator (logical f lhs rhs rawOld) arithmetic x n p I.iteratorTag I.ptag I.h_iteratorTag I.h_ptag ctx count
  (optionValue kt LiteralSyntaxValidator.lineValidator (logical f lhs rhs rawOld) arithmetic x index fuel .zero qline) index fuel
 have hcount := StationaryProof.iterationCount (T := T) (G := G) I.iteratorTag cert (.succ count)
  (state I.ptag (.succ .zero) cert) index fuel (.base hcons)
 have hpair := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := G) I.ptag _ .zero _ .zero
  hout (.base (.logical (.reflexive .zero)))
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ hcount
  (localTrans _ _ _ (.base hstep) (localTrans _ _ _ (.base hidle) hpair))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.RunProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.RunProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.RunProof.internalRawSingletonRun
