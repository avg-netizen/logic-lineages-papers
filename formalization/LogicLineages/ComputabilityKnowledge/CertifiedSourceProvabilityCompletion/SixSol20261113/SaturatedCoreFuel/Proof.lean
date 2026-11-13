module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedCoreFuel.InstallationProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedCoreFuel.WitnessTransportProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.ExtractionLogicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedCoreFuel.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph LiteralCheckerAuxiliaries
open LiteralCheckerAcceptance LiteralCheckerAcceptance.WitnessProof

theorem internalMonotonicity : Targets.InternalMonotonicity := by
 intro v l a x n p qtag hq ctx index s t context formula cert
 let T := GorbowPRNumeralCalculation.Theory p
 let X := SaturatedAxiomLeaf.saturated x
 let itag := qtag+iteratorOffset v l a X
 obtain ⟨ptag,ctag,dtag,droptag,hp,hc,hd,hdrop⟩ := InstallationProof.auxiliaries p qtag v l a X hq
 obtain ⟨_,hi⟩ := CoreProof.coreNodes p qtag v l a X hq
 obtain ⟨haccS⟩ := CoreProof.internalCoreAcceptance n p qtag ptag ctag dtag droptag v l a X hq hp hc hd hdrop ctx index s context formula cert
 obtain ⟨haccT⟩ := CoreProof.internalCoreAcceptance n p qtag ptag ctag dtag droptag v l a X hq hp hc hd hdrop ctx index t context formula cert
 let stateS := runCall itag ptag index s cert
 let stateT := runCall itag ptag index t cert
 let H := orderGuard s t
 let L2 : Term ctx → Term (ctx+1+1) := fun u => liftTerm (liftTerm u)
 let raw : Term (ctx+1+1) := liftTerm (.var (0 : Fin (ctx+1)))
 let tail : Term (ctx+1+1) := .var 0
 let final := successfulState ptag ctag (L2 context) raw tail .zero
 obtain ⟨hrun⟩ := SaturatedKernelFuel.StatementChecks.internalIterator v l a x n p itag ptag ctag hi hp hc (ctx+1+1)
  (L2 cert) (L2 index) (L2 s) (L2 t) .zero (L2 cert)
  (HistoryKernel.pairCall ctag (HistoryKernel.pairCall ptag (L2 context) raw) tail) .zero
 have hr : Derivation T (.imp (GorbowPACore.weaken (GorbowPACore.weaken H))
  (.imp (.equal (L2 stateS) final) (.equal (L2 stateT) final))) := by
  simpa only [H,L2,stateS,stateT,final,SaturatedKernelFuel.iteratorTransport,
   GorbowPACore.weaken,FuelWitness.ExtractionLogicProof.substOrder,
   runCall,SixSol20261112.HistoryMachine.iterationCall,successfulState,HistoryKernel.pairCall,
   liftTerm,renameTerm,Logic.substCall,substitute,List.Vector.map_cons,List.Vector.map_nil] using hrun
 let A := inner ptag ctag (liftTerm stateS) (liftTerm context) (liftTerm formula) (.var 0)
 let B := inner ptag ctag (liftTerm stateT) (liftTerm context) (liftTerm formula) (.var 0)
 let H2 := GorbowPACore.weaken (GorbowPACore.weaken H)
 have hh : Hilbert.Local T (ctx+1+1) [A,H2] H2 := .hypothesis (by simp)
 have ha : Hilbert.Local T (ctx+1+1) [A,H2] A := .hypothesis List.mem_cons_self
 have heq := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) ha
 have hstate := Hilbert.Local.mp (.base (.logical (.andRight _ _))) ha
 have hnew := Hilbert.Local.mp (.mp (.base hr) hh) hstate
 have hb : Hilbert.Local T (ctx+1+1) [A,H2] B :=
  .mp (.mp (.base (.logical (.andIntro _ _))) heq) hnew
 obtain ⟨hmap⟩ := WitnessTransportProof.transportWitness T ptag ctag stateS stateT context formula H
  (Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hb)))
 have hs : Derivation T (.imp (SaturatedCoreFuel.acceptance qtag index s context formula cert)
  (witness ptag ctag stateS context formula)) := by
  simpa only [LiteralCheckerAcceptance.acceptance,frozenWitness,stateS,itag,X,SaturatedCoreFuel.acceptance] using
   Derivation.mp (.logical (.andLeft _ _)) haccS
 have ht : Derivation T (.imp (witness ptag ctag stateT context formula)
  (SaturatedCoreFuel.acceptance qtag index t context formula cert)) := by
  simpa only [LiteralCheckerAcceptance.acceptance,frozenWitness,stateT,itag,X,SaturatedCoreFuel.acceptance] using
   Derivation.mp (.logical (.andRight _ _)) haccT
 let Old := SaturatedCoreFuel.acceptance qtag index s context formula cert
 have hold : Hilbert.Local T ctx [Old,H] Old := .hypothesis List.mem_cons_self
 have hbound : Hilbert.Local T ctx [Old,H] H := .hypothesis (by simp)
 have hresult := Hilbert.Local.mp (.base ht) (.mp (.mp (.base hmap) hbound) (.mp (.base hs) hold))
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hresult))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedCoreFuel.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedCoreFuel.Proof
