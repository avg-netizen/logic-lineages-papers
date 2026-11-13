module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.CasesProof

public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.InductionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open HistoryLengthOffset SupportProof
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport BoundedProof CasesProof

theorem zeroAll {n ctx : Nat} (p : Program n) (itag ltag  ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) ( index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (allBounded itag ltag  ptag .zero  index fuel)) := by
  obtain ⟨hz⟩ := allCodes p itag ltag  ptag ctag v l a x hi hl  hp hc false (.zero : Term (ctx+1)) (.var 0)  (liftTerm index) (liftTerm fuel)
  exact ⟨.generalize hz⟩

theorem successorAll {n ctx : Nat} (p : Program n) (itag ltag  ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (count  index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (allBounded itag ltag  ptag count  index fuel) (allBounded itag ltag  ptag (.succ count)  index fuel))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let P := allBounded itag ltag  ptag count  index fuel
  let Q := bounded itag ltag  ptag (.succ (liftTerm count)) (.var (0 : Fin (ctx+1)))  (liftTerm index) (liftTerm fuel)
  obtain ⟨hs⟩ := allCodes p itag ltag  ptag ctag v l a x hi hl  hp hc true (liftTerm count) (.var (0 : Fin (ctx+1)))  (liftTerm index) (liftTerm fuel)
  have hs' : Derivation T (.imp (GorbowPACore.weaken P) Q) := by
    simpa only [P,Q,GorbowPACore.weaken,substAll,liftTerm,renameTerm,phase,if_true] using hs
  have hd := Derivation.mp (.logical (.allDistribute (GorbowPACore.weaken P) Q)) (.generalize hs')
  exact ⟨Hilbert.compose hd (.logical (.allVacuous P))⟩

def template {ctx : Nat} (itag ltag  ptag : Nat) ( index fuel : Term ctx) : Formula (ctx+1) :=
  allBounded itag ltag  ptag (.var 0)  (liftTerm index) (liftTerm fuel)
theorem templateAt {ctx : Nat} (itag ltag  ptag : Nat) ( index fuel count : Term ctx) :
    GorbowStandardInstances.instantiate (template itag ltag  ptag  index fuel) count=
      allBounded itag ltag  ptag count  index fuel := by
  simp only [GorbowStandardInstances.instantiate,template,substAll,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem lengthProperty {n ctx : Nat} (p : Program n) (itag ltag  ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (left  index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (property itag ltag  ptag left  index fuel)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := template itag ltag  ptag  index fuel
  obtain ⟨hz⟩ := zeroAll p itag ltag  ptag ctag v l a x hi hl  hp hc  index fuel
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi=template itag ltag  ptag  index fuel from rfl,templateAt]
    exact hz
  obtain ⟨hs0⟩ := successorAll p itag ltag  ptag ctag v l a x hi hl  hp hc (.var (0 : Fin (ctx+1)))  (liftTerm index) (liftTerm fuel)
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simpa only [phi,template,GorbowStandardInduction.successorInstance,substAll,substitute,successorLift,Fin.cases_zero] using hs0
  have hall := atTerm phi (lengthCall ltag left) (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  rw [show phi=template itag ltag  ptag  index fuel from rfl,templateAt] at hall
  exact ⟨.mp (.mp (allElim itag ltag  ptag (lengthCall ltag left) left  index fuel) hall) (.logical (.reflexive _))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.InductionProof

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.InductionProof
