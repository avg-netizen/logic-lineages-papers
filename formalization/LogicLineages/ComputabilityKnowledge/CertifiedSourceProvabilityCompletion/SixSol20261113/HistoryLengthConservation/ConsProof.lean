module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.SomeStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.ConsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryLengthOffset HistoryRunSplice SupportProof

theorem consProperty {n ctx : Nat} (p : Program n) (itag ltag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (line tail index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (property itag ltag ptag tail index fuel)
        (property itag ltag ptag (HistoryLookup.consCall ctag line tail) index fuel))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let P := property itag ltag ptag tail index fuel
  obtain ⟨hn⟩ := StepSupportProof.noneCons p itag ltag ptag ctag v l a x hi hl hp hc
    (liftTerm line) (liftTerm tail) (.var (0 : Fin (ctx+1))) (liftTerm index) (liftTerm fuel)
  have hn' : Derivation T (.imp (GorbowPACore.weaken P)
    (noneRelation itag ltag ptag (HistoryLookup.consCall ctag (liftTerm line) (liftTerm tail)) (.var 0) (liftTerm index) (liftTerm fuel))) := by
    simpa only [T,P,GorbowPACore.weaken,substProperty,liftTerm,renameTerm] using hn
  have hnone0 := HistoryIteratorSuffix.RelationProof.universalUnder P _ hn'
  have hnone : Derivation T (.imp P (noneAll itag ltag ptag (HistoryLookup.consCall ctag line tail) index fuel)) := by
    simpa only [noneAll,liftTerm,renameTerm,HistoryLookup.consCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil] using hnone0
  let L := liftTerm (liftTerm line)
  let C := liftTerm (liftTerm tail)
  let I := liftTerm (liftTerm index)
  let F := liftTerm (liftTerm fuel)
  obtain ⟨hs⟩ := SomeStepProof.someCons p itag ltag ptag ctag v l a x hi hl hp hc L C (.var (1 : Fin (ctx+2))) (.var 0) I F
  have hs' : Derivation T (.imp (GorbowPACore.weaken (GorbowPACore.weaken P))
    (someRelation itag ltag ptag (HistoryLookup.consCall ctag L C) (.var 1) (.var 0) I F)) := by
    simpa only [T,P,L,C,I,F,GorbowPACore.weaken,substProperty,liftTerm,renameTerm] using hs
  have hs0 := HistoryIteratorSuffix.RelationProof.universalUnder P _
    (HistoryIteratorSuffix.RelationProof.universalUnder (GorbowPACore.weaken P) _ hs')
  have hvar : Fin.succ (0 : Fin (ctx+1)) = (1 : Fin (ctx+2)) := by
    apply Fin.ext
    rfl
  have hsome : Derivation T (.imp P (someAll itag ltag ptag (HistoryLookup.consCall ctag line tail) index fuel)) := by
    simpa only [someAll,someOut,L,C,I,F,liftTerm,renameTerm,HistoryLookup.consCall,Logic.substCall,
      List.Vector.map_cons,List.Vector.map_nil,substitute,hvar] using hs0
  have hP : Hilbert.Local T ctx [P] P := .hypothesis List.mem_cons_self
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
    (.mp (.mp (.base (.logical (.andIntro _ _))) (.mp (.base hnone) hP)) (.mp (.base hsome) hP)))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.ConsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.ConsProof
