module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.AuxiliaryStatements
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.LeafDispatcherDispatcherProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.Kernel.Proof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryKernel HistoryKernel.EntryProof HistoryKernel.TransitionEquationsProof HistoryKernel.OptionProof

variable (test : Program 1)

theorem internalActiveStep : Targets.InternalActiveStep test := by
 intro n p valid old arithmetic x ot nt ptag ctag ho hn hp hc ctx index fuel h line rest out
 let T := GorbowPRNumeralCalculation.Theory p
 let refined := extend test old
 let E := Formula.equal (kernelCall ot (activeState ptag ctag h line rest) index fuel) (pairCall ptag (.succ out) rest)
 let N := newHistory (someTag ot valid old arithmetic x) h line
 let N' := newHistory (someTag nt valid refined arithmetic x) h line
 obtain ⟨_,_,_,hod,_⟩ := kernelNodes p ot valid old arithmetic x ho
 obtain ⟨hpair,_,_,hnd,_⟩ := kernelNodes p nt valid refined arithmetic x hn
 obtain ⟨hparts⟩ := HistoryKernel.SuccessProof.successfulParts p ot ptag ctag valid old arithmetic x ho hp hc index fuel h line rest out
 obtain ⟨hd⟩ := UniformClosedRule12CoreRetention.Generic.LeafDispatcher.DispatcherProof.internalDispatcherRetention test n p valid old arithmetic x
  (dispatcherTag ot valid old arithmetic x) (dispatcherTag nt valid refined arithmetic x) hod hnd ctx index fuel h line
 obtain ⟨hopt⟩ := optionAccepted p nt valid refined arithmetic x hn index fuel h line
 obtain ⟨hnew⟩ := HistoryKernel.NormalProof.kernelEquation p nt ptag ctag valid refined arithmetic x hn hp hc index fuel h line rest
 have hso := someInstalled p ot valid old arithmetic x ho
 have hsn := someInstalled p nt valid refined arithmetic x hn
 obtain ⟨heo⟩ := someEquation p (someTag ot valid old arithmetic x) ptag ctag hso hp hc index fuel h line rest
 obtain ⟨hen⟩ := someEquation p (someTag nt valid refined arithmetic x) ptag ctag hsn hp hc index fuel h line rest
 obtain ⟨hcoh⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p
  (someTag nt valid refined arithmetic x) (someTag ot valid old arithmetic x) 3 someExtendedHistory hsn hso ctx
  (HistoryKernel.FieldsProof.activeArgs ptag ctag index fuel h line rest)
 have hhist : Derivation T (.equal (.succ N') (.succ N)) :=
  Logic.trans _ _ _ (Support.equalitySymmetry _ _ hen) (Logic.trans _ _ _ hcoh heo)
 obtain ⟨hcopy⟩ := HistoryDecoder.PairCongruenceProof.pairCopies p (outputPairTag nt valid refined arithmetic x) ptag hpair hp (.succ out) rest
 have e : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
 have parts := Hilbert.Local.mp (.base hparts) e
 have oldCheck := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) parts
 have oldShape := Hilbert.Local.mp (.base (.logical (.andRight _ _))) parts
 have newCheck := Hilbert.Local.mp (.base hd) oldCheck
 have optionShape := Hilbert.Local.mp (.base hopt) newCheck
 have successorShape : Hilbert.Local T ctx [E] (.equal (.succ N') (.succ out)) :=
  localTrans _ _ _ (.base hhist) (localUnary (.succ (.var 0)) N out oldShape)
 have pairOption := HistoryKernel.SuffixProof.firstCongruence (outputPairTag nt valid refined arithmetic x) _ _ rest optionShape
 have pairHistory := HistoryKernel.SuffixProof.firstCongruence (outputPairTag nt valid refined arithmetic x) _ _ rest successorShape
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ (.base hnew)
  (localTrans _ _ _ pairOption (localTrans _ _ _ pairHistory (.base hcopy)))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.Kernel.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.Kernel.Proof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.Kernel.Proof.internalActiveStep
