module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.CasesProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.CompletenessProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.CoreProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowTheoryProof
open SixSol20261112.Fuel NamedArithmeticGraph LiteralCheckerAuxiliaries WitnessProof
open HistoryCodec.ArithmeticSupport

theorem coreNodes {n : Nat} (p : Program n) (qtag : Nat) (v l a : Program 1) (x : Program 3)
    (hq : (nodes p)[qtag]? = some ⟨5,LiteralKernelSource.coreChecker v l a x bound initial finalizer⟩) :
    (nodes p)[qtag+1]? = some ⟨4,finalizer⟩ ∧
    (nodes p)[qtag+iteratorOffset v l a x]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩ := by
  let k := HistoryKernel.kernel v l a x
  have hf := Equations.functionChild p qtag finalizer (SixSol20261112.HistoryMachine.checkerArguments k bound initial) hq
  have hl := Equations.argumentChild p qtag finalizer (SixSol20261112.HistoryMachine.checkerArguments k bound initial) hq 0
  have hi := Equations.functionChild p _ (SixSol20261112.HistoryMachine.iterator k)
    (SixSol20261112.HistoryMachine.loopArguments bound initial) hl
  exact ⟨hf,by simpa only [iteratorOffset,Nat.add_assoc] using hi⟩

theorem internalCoreAcceptance : Targets.InternalCoreAcceptance := by
  intro n p qtag ptag ctag dtag droptag v l a x hq hp hc hd hdrop ctx index fuel context formula certificate
  let T := GorbowPRNumeralCalculation.Theory p
  let itag := qtag+iteratorOffset v l a x
  let state := runCall itag ptag index fuel certificate
  let qvalue := coreCall qtag index fuel context formula certificate
  let fvalue := finalCall (qtag+1) state context formula certificate
  let A := Formula.equal qvalue (.succ .zero)
  let W := witness ptag ctag state context formula
  obtain ⟨hf,hi⟩ := coreNodes p qtag v l a x hq
  obtain ⟨hn⟩ := NormalizationProof.internalCoreNormalization n p qtag ptag v l a x hq hp ctx index fuel context formula certificate
  obtain ⟨hdrain⟩ := HistoryIteratorDrain.IterationProof.internalIteratorDrain v l a x n p itag dtag droptag ptag ctag hi hd hdrop hp hc ctx (.succ .zero) certificate index fuel
  obtain ⟨hs⟩ := CasesProof.allSound p (qtag+1) dtag ptag ctag hf hd hp hc state context formula certificate
  have ha : Hilbert.Local T ctx [A] A := .hypothesis List.mem_cons_self
  have hfinal : Hilbert.Local T ctx [A] (.equal fvalue (.succ .zero)) :=
    localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (.base hn)) ha
  have hw : Hilbert.Local T ctx [A] W := .mp (.mp (.base hs) hfinal) (.base hdrain)
  have forward : Derivation T (.imp A W) := Hilbert.Local.finish (Hilbert.Local.discharge hw)
  obtain ⟨hcomplete⟩ := CompletenessProof.completeWitness p (qtag+1) ptag ctag hf hp hc state context formula certificate
  have hw' : Hilbert.Local T ctx [W] W := .hypothesis List.mem_cons_self
  have hfinal' := Hilbert.Local.mp (.base hcomplete) hw'
  have reverse : Derivation T (.imp W A) := Hilbert.Local.finish (Hilbert.Local.discharge
    (localTrans _ _ _ (.base hn) hfinal'))
  have result := Derivation.mp (.mp (.logical (.andIntro _ _)) forward) reverse
  simpa only [acceptance,frozenWitness,A,W,qvalue,state,itag] using (show Nonempty (Derivation T _) from ⟨result⟩)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.CoreProof
