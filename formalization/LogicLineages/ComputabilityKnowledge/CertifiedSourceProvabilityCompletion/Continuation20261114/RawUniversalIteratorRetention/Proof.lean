module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalIteratorRetention.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalIteratorRetention.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel SixSol20261112.HistoryMachine NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryKernel RawUniversalSimulation RawUniversalSimulation.RelationProof RawUniversalSimulation.SupportProof
theorem oldAt {ctx : Nat} ptag (old new  : Term ctx) :
    GorbowStandardInstances.instantiate (relation ptag (.var 0) (liftTerm new) ) old =
      relation ptag old new  := by
  simp only [GorbowStandardInstances.instantiate,substRelation,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
theorem newAt {ctx : Nat} ptag (old new  : Term ctx) :
    GorbowStandardInstances.instantiate (relation ptag (liftTerm old) (.var 0) ) new =
      relation ptag old new  := by
  simp only [GorbowStandardInstances.instantiate,substRelation,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

noncomputable def relationOld {T : Sentence → Prop} {ctx : Nat} ptag (old old' new  : Term ctx) :
    Derivation T (.imp (.equal old old') (.imp (relation ptag old new ) (relation ptag old' new ))) := by
  have h := Derivation.logical (A := T) (.equalityReplace (relation ptag (.var 0) (liftTerm new) ) old old')
  rwa [GorbowPACore.logicalFormula,oldAt,oldAt] at h
noncomputable def relationNew {T : Sentence → Prop} {ctx : Nat} ptag (old new new'  : Term ctx) :
    Derivation T (.imp (.equal new new') (.imp (relation ptag old new ) (relation ptag old new' ))) := by
  have h := Derivation.logical (A := T) (.equalityReplace (relation ptag (liftTerm old) (.var 0) ) new new')
  rwa [GorbowPACore.logicalFormula,newAt,newAt] at h

noncomputable def relationReverse {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)} ptag
    (old new old' new'  : Term ctx) (ho : Derivation T (.equal old old')) (hn : Derivation T (.equal new new'))
    (hr : Hilbert.Local T ctx G (relation ptag old' new' )) :
    Hilbert.Local T ctx G (relation ptag old new ) :=
  .mp (.mp (.base (relationNew ptag old new' new )) (.base (Support.equalitySymmetry _ _ hn)))
    (.mp (.mp (.base (relationOld ptag old' old new' )) (.base (Support.equalitySymmetry _ _ ho))) hr)

theorem substIteration {m n : Nat} (sub : Fin m → Term n) itag (count state index fuel : Term m) :
    substitute sub (iterationCall itag count state index fuel) =
      iterationCall itag (substitute sub count) (substitute sub state) (substitute sub index) (substitute sub fuel) := by
  simp only [iterationCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]

def template {ctx : Nat} (ot nt ptag : Nat) (old new  index fuel : Term ctx) : Formula (ctx+1) :=
  relation ptag (iterationCall ot (.var 0) (liftTerm old) (liftTerm index) (liftTerm fuel))
    (iterationCall nt (.var 0) (liftTerm new) (liftTerm index) (liftTerm fuel)) 

theorem templateAt {ctx : Nat} ot nt ptag (old new  index fuel count : Term ctx) :
    GorbowStandardInstances.instantiate (template ot nt ptag old new  index fuel) count =
      relation ptag (iterationCall ot count old index fuel) (iterationCall nt count new index fuel)  := by
  simp only [GorbowStandardInstances.instantiate,template,substRelation,substIteration,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

/-- Genuine PA iteration induction. The sole helper premise is the base state
relation; the exported target constructs it, and the actual kernel step is proved. -/
theorem iterateRelation {n ctx : Nat} (p : Program n) (ot nt ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (ho : (nodes p)[ot]? = some ⟨4,iterator (kernel v l a x)⟩)
    (hn : (nodes p)[nt]? = some ⟨4,iterator (kernel v (RawUniversalReplace.logicalLeaf l) a x)⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (old new  index fuel count : Term ctx)
    (hrel : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (relation ptag old new ))) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (relation ptag (iterationCall ot count old index fuel) (iterationCall nt count new index fuel) )) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := template ot nt ptag old new  index fuel
  obtain ⟨hr⟩ := hrel
  obtain ⟨hoz⟩ := HistoryMachine.Equations.zero p ot (kernel v l a x) ho old index fuel
  obtain ⟨hnz⟩ := HistoryMachine.Equations.zero p nt (kernel v (RawUniversalReplace.logicalLeaf l) a x) hn new index fuel
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = template ot nt ptag old new  index fuel from rfl,templateAt]
    exact Hilbert.Local.finish (relationReverse ptag _ _ _ _  hoz hnz (.base hr))
  let O := iterationCall ot (.var (0 : Fin (ctx+1))) (liftTerm old) (liftTerm index) (liftTerm fuel)
  let N := iterationCall nt (.var (0 : Fin (ctx+1))) (liftTerm new) (liftTerm index) (liftTerm fuel)
  have hk := Equations.functionChild p (ot+stepTag iterationBase) (kernel v l a x) iterationArguments
    (Equations.recursionStepChild p ot iterationBase (iterationStep (kernel v l a x)) ho)
  have hk' := Equations.functionChild p (nt+stepTag iterationBase) (kernel v (RawUniversalReplace.logicalLeaf l) a x) iterationArguments
    (Equations.recursionStepChild p nt iterationBase (iterationStep (kernel v (RawUniversalReplace.logicalLeaf l) a x)) hn)
  obtain ⟨hstep⟩ := RawUniversalSimulation.StatementChecks.exactKernelSimulation n p v l a x
    (ot+stepTag iterationBase+1) (nt+stepTag iterationBase+1) ptag ctag hk hk' hp hc (ctx+1)
    O N (liftTerm index) (liftTerm fuel)
  have ih : Hilbert.Local T (ctx+1) [phi] (relation ptag O N ) := .hypothesis List.mem_cons_self
  have next := Hilbert.Local.mp (.base hstep) ih
  obtain ⟨hos⟩ := HistoryMachine.Equations.successor p ot (kernel v l a x) ho (.var (0 : Fin (ctx+1)))
    (liftTerm old) (liftTerm index) (liftTerm fuel)
  obtain ⟨hns⟩ := HistoryMachine.Equations.successor p nt (kernel v (RawUniversalReplace.logicalLeaf l) a x) hn (.var (0 : Fin (ctx+1)))
    (liftTerm new) (liftTerm index) (liftTerm fuel)
  have hout := relationReverse ptag _ _ _ _  hos hns next
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simpa only [phi,template,O,N,GorbowStandardInduction.successorInstance,substRelation,substIteration,
      substitute,successorLift,Fin.cases_zero] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
  have h := atTerm phi count (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  exact ⟨by simpa only [phi,templateAt] using h⟩

/-- Same initial state supplies the invariant without any shape assumption. -/
theorem reflexiveRelation {T : Sentence → Prop} {ctx : Nat} (ptag : Nat) (state : Term ctx) :
 Nonempty (Derivation T (relation ptag state state)) := by
 let B := body ptag (liftTerm (liftTerm state)) (liftTerm (liftTerm state))
  (.var (Fin.succ (0 : Fin (ctx+1)))) (.var 0)
 have h : Derivation T B := Hilbert.identity _
 exact ⟨by simpa only [relation,inner,B,liftTerm,renameTerm,substitute] using Derivation.generalize (Derivation.generalize h)⟩

theorem internalIteratorRetention : Targets.InternalIteratorRetention := by
 intro n p v l a x ot nt ptag ctag ho hn hp hc ctx count state index fuel out rest
 obtain ⟨hr⟩ := iterateRelation p ot nt ptag ctag v l a x ho hn hp hc state state index fuel count
  (reflexiveRelation ptag state)
 exact ⟨.mp (instanceRule ptag _ _ out rest) hr⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalIteratorRetention.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalIteratorRetention.Proof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalIteratorRetention.Proof.internalIteratorRetention
