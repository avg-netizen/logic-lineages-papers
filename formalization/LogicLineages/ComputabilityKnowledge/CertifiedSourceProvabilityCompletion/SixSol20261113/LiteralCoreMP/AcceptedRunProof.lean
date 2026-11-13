module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP.TailProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP.AcceptedRunProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralValidatedMPRun LiteralCheckerAcceptance LiteralCheckerAcceptance.WitnessProof TailProof

noncomputable def transportState {T : Sentence → Prop} {ctx : Nat} ptag ctag (a b context raw : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (tailWitness ptag ctag a context raw) (tailWitness ptag ctag b context raw))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (tailWitness ptag ctag (.var 0) (liftTerm context) (liftTerm raw)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substTail,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h

theorem tailRun {ctx : Nat} itag ptag ctag (context raw certificate index fuel : Term ctx) :
 tailWitness ptag ctag (runCall itag ptag index fuel certificate) context raw =
 successfulRun itag ptag ctag context raw certificate index fuel := by
 simp only [tailWitness,tailBody,successfulRun,runCall,HistoryRunSplice.run,
  SixSol20261112.HistoryMachine.iterationCall,HistoryRunSplice.state,LiteralCheckerAuxiliaries.successfulState,
  HistoryKernel.pairCall,HistoryLookup.consCall,liftTerm,renameTerm,Logic.substCall,substitute,
  List.Vector.map_cons,List.Vector.map_nil]

theorem internalAcceptedRun : Targets.InternalAcceptedRun := by
 intro l a x n p qtag itag ptag ctag dtag droptag hq hi hp hc hd hdrop ctx context raw certificate index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let it := qtag+iteratorOffset validity l a x
 let A := Formula.equal (coreCall qtag index fuel context (.add raw raw) certificate) (.succ .zero)
 obtain ⟨hacc⟩ := CoreProof.internalCoreAcceptance n p qtag ptag ctag dtag droptag validity l a x hq hp hc hd hdrop ctx index fuel context (.add raw raw) certificate
 have hfwd : Derivation T (.imp A (witness ptag ctag (runCall it ptag index fuel certificate) context (.add raw raw))) := by
  have h := Derivation.mp (.logical (.andLeft _ _)) hacc
  simpa only [acceptance,frozenWitness,A,it] using h
 obtain ⟨htail⟩ := witnessToTail T ptag ctag (runCall it ptag index fuel certificate) context raw
 obtain ⟨_,hiter⟩ := CoreProof.coreNodes p qtag validity l a x hq
 obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p it itag 4
  (SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel validity l a x)) hiter hi ctx
  (certificate ::ᵥ HistoryRunSplice.state ptag (.succ .zero) certificate ::ᵥ index ::ᵥ fuel ::ᵥ nil)
 have htransport := Derivation.mp (transportState ptag ctag
  (runCall it ptag index fuel certificate) (runCall itag ptag index fuel certificate) context raw) hcopy
 have h := Hilbert.compose htransport (Hilbert.compose htail hfwd)
 simpa only [A,tailRun] using (show Nonempty (Derivation T _) from ⟨h⟩)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP.AcceptedRunProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP.AcceptedRunProof
