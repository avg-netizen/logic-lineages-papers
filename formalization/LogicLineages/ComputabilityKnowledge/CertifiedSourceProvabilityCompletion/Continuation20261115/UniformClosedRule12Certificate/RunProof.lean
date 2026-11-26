module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Certificate.EntryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Certificate.RunProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix TwoSol20261113.ReflexivityCertificate
open SixSol20261112.Fuel SixSol20261112.HistoryMachine NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryRunSplice HistoryKernel.TransitionEquationsProof

theorem internalSingletonRun {n ctx : Nat} (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : Installation p old arithmetic x) (formula leftTerm rightTerm index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (UniformClosedRule12.guards I.fval I.vtag formula leftTerm rightTerm)
   (.equal (LiteralCheckerAcceptance.runCall I.iteratorTag I.ptag index fuel
    (certificate I.ctag I.constructorTag formula leftTerm rightTerm))
    (output I.ptag I.ctag I.caseTag I.predTag formula leftTerm rightTerm)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := UniformClosedRule12.guards I.fval I.vtag formula leftTerm rightTerm
 let G := [H]
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 let qline := UniformClosedRule12.lineCall I.constructorTag formula leftTerm rightTerm
 let cert := UniformClosedRule12Certificate.certificate I.ctag I.constructorTag formula leftTerm rightTerm
 let kt := I.iteratorTag+stepTag iterationBase+1
 let count := call (I.ctag+GorbowPRChildTags.argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0)
  (qline ::ᵥ .zero ::ᵥ nil)
 have hk := IdleProof.kernelInstalled p I.iteratorTag LiteralSyntaxValidator.lineValidator (UniformClosedRule12.logicalLeaf old) arithmetic x I.h_iterator
 obtain ⟨_,_,_,hdisp,_⟩ := HistoryKernel.OptionProof.kernelNodes p kt LiteralSyntaxValidator.lineValidator (UniformClosedRule12.logicalLeaf old) arithmetic x hk
 obtain ⟨haccept⟩ := UniformClosedRule12Dispatcher.StatementChecks.exactInternalDispatcher n p old arithmetic x
  I.toDispatcherInstallation ctx formula leftTerm rightTerm index fuel .zero
 obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p
  (dispatcherTag kt LiteralSyntaxValidator.lineValidator (UniformClosedRule12.logicalLeaf old) arithmetic x) I.dispatcherTag 4
  (UniformClosedRule12Dispatcher.dispatcher old arithmetic x) hdisp I.h_dispatcher ctx (index ::ᵥ fuel ::ᵥ .zero ::ᵥ qline ::ᵥ nil)
 obtain ⟨hoption⟩ := HistoryKernel.OptionProof.optionAccepted p kt LiteralSyntaxValidator.lineValidator (UniformClosedRule12.logicalLeaf old) arithmetic x hk index fuel .zero qline
 have ho := Hilbert.Local.mp (.base hoption)
  (localTrans _ _ _ (.base hcopy) (.mp (.base haccept) hh))
 obtain ⟨hentry⟩ := EntryProof.rawNewHistory p old arithmetic x I formula leftTerm rightTerm
  (someTag kt LiteralSyntaxValidator.lineValidator (UniformClosedRule12.logicalLeaf old) arithmetic x) (someInstalled p kt LiteralSyntaxValidator.lineValidator (UniformClosedRule12.logicalLeaf old) arithmetic x hk)
 have hs := Logic.unary (.succ (.var 0)) _ _ hentry
 have hout := localTrans _ _ _ ho (.base hs)
 obtain ⟨hcons⟩ := HistoryCodec.PairProof.internalCons n p I.ctag I.h_ctag ctx qline .zero
 obtain ⟨hstep⟩ := ConsRunProof.someCons p I.iteratorTag I.ptag I.ctag LiteralSyntaxValidator.lineValidator (UniformClosedRule12.logicalLeaf old) arithmetic x
  I.h_iterator I.h_ptag I.h_ctag count .zero qline .zero index fuel
 obtain ⟨hidle⟩ := IdleProof.internalIdle LiteralSyntaxValidator.lineValidator (UniformClosedRule12.logicalLeaf old) arithmetic x n p I.iteratorTag I.ptag I.h_iterator I.h_ptag ctx count
  (optionValue kt LiteralSyntaxValidator.lineValidator (UniformClosedRule12.logicalLeaf old) arithmetic x index fuel .zero qline) index fuel
 have hcount := StationaryProof.iterationCount (T := T) (G := G) I.iteratorTag cert (.succ count)
  (state I.ptag (.succ .zero) cert) index fuel (.base hcons)
 have hpair := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := G) I.ptag _ .zero _ .zero
  hout (.base (.logical (.reflexive .zero)))
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ hcount
  (localTrans _ _ _ (.base hstep) (localTrans _ _ _ (.base hidle) hpair))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Certificate.RunProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Certificate.RunProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Certificate.RunProof.internalSingletonRun
