module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.SimulationCasesProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.IterationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel SixSol20261112.HistoryMachine NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryKernel RelationProof SimulationProof

theorem oldAt {ctx : Nat} atag ptag (old new tail : Term ctx) :
    GorbowStandardInstances.instantiate (relation atag ptag (.var 0) (liftTerm new) (liftTerm tail)) old =
      relation atag ptag old new tail := by
  simp only [GorbowStandardInstances.instantiate,substRelation,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
theorem newAt {ctx : Nat} atag ptag (old new tail : Term ctx) :
    GorbowStandardInstances.instantiate (relation atag ptag (liftTerm old) (.var 0) (liftTerm tail)) new =
      relation atag ptag old new tail := by
  simp only [GorbowStandardInstances.instantiate,substRelation,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

noncomputable def relationOld {T : Sentence → Prop} {ctx : Nat} atag ptag (old old' new tail : Term ctx) :
    Derivation T (.imp (.equal old old') (.imp (relation atag ptag old new tail) (relation atag ptag old' new tail))) := by
  have h := Derivation.logical (A := T) (.equalityReplace (relation atag ptag (.var 0) (liftTerm new) (liftTerm tail)) old old')
  rwa [GorbowPACore.logicalFormula,oldAt,oldAt] at h
noncomputable def relationNew {T : Sentence → Prop} {ctx : Nat} atag ptag (old new new' tail : Term ctx) :
    Derivation T (.imp (.equal new new') (.imp (relation atag ptag old new tail) (relation atag ptag old new' tail))) := by
  have h := Derivation.logical (A := T) (.equalityReplace (relation atag ptag (liftTerm old) (.var 0) (liftTerm tail)) new new')
  rwa [GorbowPACore.logicalFormula,newAt,newAt] at h

noncomputable def relationReverse {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)} atag ptag
    (old new old' new' tail : Term ctx) (ho : Derivation T (.equal old old')) (hn : Derivation T (.equal new new'))
    (hr : Hilbert.Local T ctx G (relation atag ptag old' new' tail)) :
    Hilbert.Local T ctx G (relation atag ptag old new tail) :=
  .mp (.mp (.base (relationNew atag ptag old new' new tail)) (.base (Support.equalitySymmetry _ _ hn)))
    (.mp (.mp (.base (relationOld atag ptag old' old new' tail)) (.base (Support.equalitySymmetry _ _ ho))) hr)

theorem substIteration {m n : Nat} (sub : Fin m → Term n) itag (count state index fuel : Term m) :
    substitute sub (iterationCall itag count state index fuel) =
      iterationCall itag (substitute sub count) (substitute sub state) (substitute sub index) (substitute sub fuel) := by
  simp only [iterationCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]

def template {ctx : Nat} (itag atag ptag : Nat) (old new tail index fuel : Term ctx) : Formula (ctx+1) :=
  relation atag ptag (iterationCall itag (.var 0) (liftTerm old) (liftTerm index) (liftTerm fuel))
    (iterationCall itag (.var 0) (liftTerm new) (liftTerm index) (liftTerm fuel)) (liftTerm tail)

theorem templateAt {ctx : Nat} itag atag ptag (old new tail index fuel count : Term ctx) :
    GorbowStandardInstances.instantiate (template itag atag ptag old new tail index fuel) count =
      relation atag ptag (iterationCall itag count old index fuel) (iterationCall itag count new index fuel) tail := by
  simp only [GorbowStandardInstances.instantiate,template,substRelation,substIteration,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

/-- Genuine PA iteration induction. The sole helper premise is the base state
relation; the exported target constructs it, and the actual kernel step is proved. -/
theorem iterateRelation {n ctx : Nat} (p : Program n) (itag atag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[itag]? = some ⟨4,iterator (kernel v l a x)⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (old new tail index fuel count : Term ctx)
    (hrel : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (relation atag ptag old new tail))) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (relation atag ptag (iterationCall itag count old index fuel) (iterationCall itag count new index fuel) tail)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := template itag atag ptag old new tail index fuel
  obtain ⟨hr⟩ := hrel
  obtain ⟨hoz⟩ := HistoryMachine.Equations.zero p itag (kernel v l a x) ht old index fuel
  obtain ⟨hnz⟩ := HistoryMachine.Equations.zero p itag (kernel v l a x) ht new index fuel
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = template itag atag ptag old new tail index fuel from rfl,templateAt]
    exact Hilbert.Local.finish (relationReverse atag ptag _ _ _ _ tail hoz hnz (.base hr))
  let O := iterationCall itag (.var (0 : Fin (ctx+1))) (liftTerm old) (liftTerm index) (liftTerm fuel)
  let N := iterationCall itag (.var (0 : Fin (ctx+1))) (liftTerm new) (liftTerm index) (liftTerm fuel)
  have hk := Equations.functionChild p (itag+stepTag iterationBase) (kernel v l a x) iterationArguments
    (Equations.recursionStepChild p itag iterationBase (iterationStep (kernel v l a x)) ht)
  obtain ⟨hstep⟩ := SimulationCasesProof.kernelPreserves p (itag+stepTag iterationBase+1) atag ptag ctag v l a x hk ha hp hc
    O N (liftTerm tail) (liftTerm index) (liftTerm fuel)
  have ih : Hilbert.Local T (ctx+1) [phi] (relation atag ptag O N (liftTerm tail)) := .hypothesis List.mem_cons_self
  have next := Hilbert.Local.mp (.base hstep) ih
  obtain ⟨hos⟩ := HistoryMachine.Equations.successor p itag (kernel v l a x) ht (.var (0 : Fin (ctx+1)))
    (liftTerm old) (liftTerm index) (liftTerm fuel)
  obtain ⟨hns⟩ := HistoryMachine.Equations.successor p itag (kernel v l a x) ht (.var (0 : Fin (ctx+1)))
    (liftTerm new) (liftTerm index) (liftTerm fuel)
  have hout := relationReverse atag ptag _ _ _ _ (liftTerm tail) hos hns next
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simpa only [phi,template,O,N,GorbowStandardInduction.successorInstance,substRelation,substIteration,
      substitute,successorLift,Fin.cases_zero] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
  have h := atTerm phi count (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  exact ⟨by simpa only [phi,templateAt] using h⟩

theorem internalIteratorSuffix : Targets.InternalIteratorSuffix := by
  intro v l a x n p itag atag ptag ctag ht ha hp hc ctx count index fuel h tail lines out rest
  obtain ⟨hr⟩ := iterateRelation p itag atag ptag ctag v l a x ht ha hp hc
    (pairCall ptag (.succ h) lines) (pairCall ptag (.succ (pairCall atag h tail)) lines)
    tail index fuel count (initialRelation p atag ptag hp h tail lines)
  exact ⟨.mp (instanceRule atag ptag _ _ tail out rest) hr⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.IterationProof
