module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.PrefixConsProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.PrefixOptionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryLengthOffset
open PrefixSupportProof

def stepFormula {ctx : Nat} (itag ltag atag ptag ctag : Nat) (line tail right option out index fuel : Term ctx) : Formula ctx :=
  .imp (property itag ltag atag ptag tail right index fuel)
    (relation itag ltag atag ptag (HistoryLookup.consCall ctag line tail) right option out index fuel)
theorem substStep {m n : Nat} (sub : Fin m → Term n) itag ltag atag ptag ctag (line tail right option out index fuel : Term m) :
    substituteFormula sub (stepFormula itag ltag atag ptag ctag line tail right option out index fuel)=
      stepFormula itag ltag atag ptag ctag (substitute sub line) (substitute sub tail) (substitute sub right)
        (substitute sub option) (substitute sub out) (substitute sub index) (substitute sub fuel) := by
  simp only [stepFormula,substituteFormula,substProperty,substRelation,HistoryLookup.DropEquationsProof.substCons]
theorem weakenStep {ctx : Nat} itag ltag atag ptag ctag (line tail right option out index fuel : Term ctx) :
    GorbowPACore.weaken (stepFormula itag ltag atag ptag ctag line tail right option out index fuel)=
      stepFormula itag ltag atag ptag ctag (liftTerm line) (liftTerm tail) (liftTerm right) (liftTerm option) (liftTerm out) (liftTerm index) (liftTerm fuel) := by
  rw [GorbowPACore.weaken,substStep]
  rfl
noncomputable def transport {T : Sentence → Prop} {ctx : Nat} (itag ltag atag ptag ctag : Nat) (line tail right a b out index fuel : Term ctx) :
    Derivation T (.imp (.equal a b) (.imp (stepFormula itag ltag atag ptag ctag line tail right a out index fuel)
      (stepFormula itag ltag atag ptag ctag line tail right b out index fuel))) := by
  have he := Derivation.logical (A := T) (.equalityReplace
    (stepFormula itag ltag atag ptag ctag (liftTerm line) (liftTerm tail) (liftTerm right) (.var 0) (liftTerm out) (liftTerm index) (liftTerm fuel)) a b)
  simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substStep,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using he

theorem allOptions {n ctx : Nat} (p : Program n) (itag ltag atag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (line tail right option out index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (stepFormula itag ltag atag ptag ctag line tail right option out index fuel)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := stepFormula itag ltag atag ptag ctag line tail right option out index fuel
  let E := Formula.equal option .zero
  obtain ⟨hz⟩ := PrefixConsProof.noneCase p itag ltag atag ptag ctag v l a x hi hl ha hp hc line tail right out index fuel
  have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  have hzero : Derivation T (.imp E Q) := Hilbert.Local.finish (Hilbert.Local.discharge
    (.mp (.mp (.base (transport itag ltag atag ptag ctag line tail right .zero option out index fuel))
      (HistoryOrder.StepProof.localSym _ _ he)) (.base hz)))
  let H := HistoryOrder.SupportProof.predBody option
  have hh : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm option) (.succ (.var 0))) := .hypothesis List.mem_cons_self
  obtain ⟨hn⟩ := PrefixConsProof.someCase p itag ltag atag ptag ctag v l a x hi hl ha hp hc
    (liftTerm line) (liftTerm tail) (liftTerm right) (.var (0 : Fin (ctx+1))) (liftTerm out) (liftTerm index) (liftTerm fuel)
  have hout := Hilbert.Local.mp (.mp (.base (transport itag ltag atag ptag ctag (liftTerm line) (liftTerm tail) (liftTerm right)
    _ _ (liftTerm out) (liftTerm index) (liftTerm fuel))) (HistoryOrder.StepProof.localSym _ _ hh)) (.base hn)
  have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
    simpa only [Q,weakenStep] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
  obtain ⟨helim⟩ := HBQuantifier.existentialElimination T H Q ⟨hb⟩
  obtain ⟨hs⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T option
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzero) helim) hs⟩

theorem consProperty {n ctx : Nat} (p : Program n) (itag ltag atag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (line tail right index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (property itag ltag atag ptag tail right index fuel)
        (property itag ltag atag ptag (HistoryLookup.consCall ctag line tail) right index fuel))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let P := property itag ltag atag ptag tail right index fuel
  let L := liftTerm (liftTerm line)
  let C := liftTerm (liftTerm tail)
  let R := liftTerm (liftTerm right)
  let I := liftTerm (liftTerm index)
  let F := liftTerm (liftTerm fuel)
  obtain ⟨hs⟩ := allOptions p itag ltag atag ptag ctag v l a x hi hl ha hp hc L C R (.var (1 : Fin (ctx+2))) (.var 0) I F
  have hs' : Derivation T (.imp (GorbowPACore.weaken (GorbowPACore.weaken P))
    (relation itag ltag atag ptag (HistoryLookup.consCall ctag L C) R (.var 1) (.var 0) I F)) := by
    simpa only [P,T,L,C,R,I,F,stepFormula,GorbowPACore.weaken,substProperty,liftTerm,renameTerm] using hs
  have ho := HistoryIteratorSuffix.RelationProof.universalUnder (GorbowPACore.weaken P) _ hs'
  have hall := HistoryIteratorSuffix.RelationProof.universalUnder P _ ho
  have hvar : Fin.succ (0 : Fin (ctx+1)) = (1 : Fin (ctx+2)) := by
    apply Fin.ext
    rfl
  refine ⟨?_⟩
  simpa only [P,T,property,oneOption,L,C,R,I,F,liftTerm,renameTerm,
    HistoryLookup.consCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute,hvar] using hall

theorem nilProperty {n ctx : Nat} (p : Program n) (itag ltag atag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (right index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (property itag ltag atag ptag .zero right index fuel)) := by
  obtain ⟨hz⟩ := nilRelation p itag ltag atag ptag v l a x hi hl ha hp
    (liftTerm (liftTerm right)) (.var (1 : Fin (ctx+2))) (.var 0) (liftTerm (liftTerm index)) (liftTerm (liftTerm fuel))
  exact ⟨.generalize (.generalize hz)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.PrefixOptionProof

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.PrefixOptionProof
