module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.EqualityInstantiationCoreRetention.SimulationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.EqualityInstantiationCoreRetention.Iteration.Proof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open RawUniversalIteratorRetention.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel SixSol20261112.HistoryMachine NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryKernel RawUniversalSimulation RawUniversalSimulation.RelationProof RawUniversalSimulation.SupportProof
theorem iterateRelation {n ctx : Nat} (lhs rhs : Term 1) (p : Program n) (ot nt ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (ho : (nodes p)[ot]? = some ⟨4,iterator (kernel v l a x)⟩)
    (hn : (nodes p)[nt]? = some ⟨4,iterator (kernel v (RawEqualityInstantiationAcceptance.logicalLeaf lhs rhs l) a x)⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (old new  index fuel count : Term ctx)
    (hrel : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (relation ptag old new ))) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (relation ptag (iterationCall ot count old index fuel) (iterationCall nt count new index fuel) )) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := template ot nt ptag old new  index fuel
  obtain ⟨hr⟩ := hrel
  obtain ⟨hoz⟩ := HistoryMachine.Equations.zero p ot (kernel v l a x) ho old index fuel
  obtain ⟨hnz⟩ := HistoryMachine.Equations.zero p nt (kernel v (RawEqualityInstantiationAcceptance.logicalLeaf lhs rhs l) a x) hn new index fuel
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = template ot nt ptag old new  index fuel from rfl,templateAt]
    exact Hilbert.Local.finish (relationReverse ptag _ _ _ _  hoz hnz (.base hr))
  let O := iterationCall ot (.var (0 : Fin (ctx+1))) (liftTerm old) (liftTerm index) (liftTerm fuel)
  let N := iterationCall nt (.var (0 : Fin (ctx+1))) (liftTerm new) (liftTerm index) (liftTerm fuel)
  have hk := Equations.functionChild p (ot+stepTag iterationBase) (kernel v l a x) iterationArguments
    (Equations.recursionStepChild p ot iterationBase (iterationStep (kernel v l a x)) ho)
  have hk' := Equations.functionChild p (nt+stepTag iterationBase) (kernel v (RawEqualityInstantiationAcceptance.logicalLeaf lhs rhs l) a x) iterationArguments
    (Equations.recursionStepChild p nt iterationBase (iterationStep (kernel v (RawEqualityInstantiationAcceptance.logicalLeaf lhs rhs l) a x)) hn)
  obtain ⟨hstep⟩ := Simulation.Proof.internalKernelSimulation lhs rhs n p v l a x
    (ot+stepTag iterationBase+1) (nt+stepTag iterationBase+1) ptag ctag hk hk' hp hc (ctx+1)
    O N (liftTerm index) (liftTerm fuel)
  have ih : Hilbert.Local T (ctx+1) [phi] (relation ptag O N ) := .hypothesis List.mem_cons_self
  have next := Hilbert.Local.mp (.base hstep) ih
  obtain ⟨hos⟩ := HistoryMachine.Equations.successor p ot (kernel v l a x) ho (.var (0 : Fin (ctx+1)))
    (liftTerm old) (liftTerm index) (liftTerm fuel)
  obtain ⟨hns⟩ := HistoryMachine.Equations.successor p nt (kernel v (RawEqualityInstantiationAcceptance.logicalLeaf lhs rhs l) a x) hn (.var (0 : Fin (ctx+1)))
    (liftTerm new) (liftTerm index) (liftTerm fuel)
  have hout := relationReverse ptag _ _ _ _  hos hns next
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simpa only [phi,template,O,N,GorbowStandardInduction.successorInstance,substRelation,substIteration,
      substitute,successorLift,Fin.cases_zero] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
  have h := atTerm phi count (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  exact ⟨by simpa only [phi,templateAt] using h⟩

/-- Same initial state supplies the invariant without any shape assumption. -/
theorem internalIteratorRetention : Targets.InternalIteratorRetention := by
 intro lhs rhs n p v l a x ot nt ptag ctag ho hn hp hc ctx count state index fuel out rest
 obtain ⟨hr⟩ := iterateRelation lhs rhs p ot nt ptag ctag v l a x ho hn hp hc state state index fuel count
  (reflexiveRelation ptag state)
 exact ⟨.mp (instanceRule ptag _ _ out rest) hr⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.EqualityInstantiationCoreRetention.Iteration.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.EqualityInstantiationCoreRetention.Iteration.Proof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.EqualityInstantiationCoreRetention.Iteration.Proof.internalIteratorRetention
