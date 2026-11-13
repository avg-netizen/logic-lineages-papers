module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.PrefixCasesProof

public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.PrefixInductionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open HistoryLengthOffset PrefixSupportProof
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport PrefixBoundedProof PrefixCasesProof

theorem zeroAll {n ctx : Nat} (p : Program n) (itag ltag atag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (right index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (allBounded itag ltag atag ptag .zero right index fuel)) := by
  obtain ⟨hz⟩ := allCodes p itag ltag atag ptag ctag v l a x hi hl ha hp hc false (.zero : Term (ctx+1)) (.var 0) (liftTerm right) (liftTerm index) (liftTerm fuel)
  exact ⟨.generalize hz⟩

theorem successorAll {n ctx : Nat} (p : Program n) (itag ltag atag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (count right index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (allBounded itag ltag atag ptag count right index fuel) (allBounded itag ltag atag ptag (.succ count) right index fuel))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let P := allBounded itag ltag atag ptag count right index fuel
  let Q := bounded itag ltag atag ptag (.succ (liftTerm count)) (.var (0 : Fin (ctx+1))) (liftTerm right) (liftTerm index) (liftTerm fuel)
  obtain ⟨hs⟩ := allCodes p itag ltag atag ptag ctag v l a x hi hl ha hp hc true (liftTerm count) (.var (0 : Fin (ctx+1))) (liftTerm right) (liftTerm index) (liftTerm fuel)
  have hs' : Derivation T (.imp (GorbowPACore.weaken P) Q) := by
    simpa only [P,Q,GorbowPACore.weaken,substAll,liftTerm,renameTerm,phase,if_true] using hs
  have hd := Derivation.mp (.logical (.allDistribute (GorbowPACore.weaken P) Q)) (.generalize hs')
  exact ⟨Hilbert.compose hd (.logical (.allVacuous P))⟩

def template {ctx : Nat} (itag ltag atag ptag : Nat) (right index fuel : Term ctx) : Formula (ctx+1) :=
  allBounded itag ltag atag ptag (.var 0) (liftTerm right) (liftTerm index) (liftTerm fuel)
theorem templateAt {ctx : Nat} (itag ltag atag ptag : Nat) (right index fuel count : Term ctx) :
    GorbowStandardInstances.instantiate (template itag ltag atag ptag right index fuel) count=
      allBounded itag ltag atag ptag count right index fuel := by
  simp only [GorbowStandardInstances.instantiate,template,substAll,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem prefixProperty {n ctx : Nat} (p : Program n) (itag ltag atag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (left right index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (property itag ltag atag ptag left right index fuel)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := template itag ltag atag ptag right index fuel
  obtain ⟨hz⟩ := zeroAll p itag ltag atag ptag ctag v l a x hi hl ha hp hc right index fuel
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi=template itag ltag atag ptag right index fuel from rfl,templateAt]
    exact hz
  obtain ⟨hs0⟩ := successorAll p itag ltag atag ptag ctag v l a x hi hl ha hp hc (.var (0 : Fin (ctx+1))) (liftTerm right) (liftTerm index) (liftTerm fuel)
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simpa only [phi,template,GorbowStandardInduction.successorInstance,substAll,substitute,successorLift,Fin.cases_zero] using hs0
  have hall := atTerm phi (lengthCall ltag left) (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  rw [show phi=template itag ltag atag ptag right index fuel from rfl,templateAt] at hall
  exact ⟨.mp (.mp (allElim itag ltag atag ptag (lengthCall ltag left) left right index fuel) hall) (.logical (.reflexive _))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.PrefixInductionProof

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.PrefixInductionProof
