module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestSuccIteration.InvariantProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestSuccIteration.IterationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open InvariantProof

theorem zero {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (s : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (iteratorCall I.iteratorTag .zero s) s)) := by
 let base : Program 1 := .projection 0
 let st : Program 3 := HistoryRuleSuffix.applyOne step (.projection 1)
 have hi : (nodes p)[I.iteratorTag]? = some ⟨2, .recursion base st⟩ := I.hiterator
 have hb : (nodes p)[I.iteratorTag+1]? = some ⟨1,base⟩ :=
  GorbowPRSubtree.Proof.lookupTransport n p I.iteratorTag ⟨2,iterator⟩ 1 ⟨1,base⟩ I.hiterator
   (GorbowPRChildTags.Proof.recursionBase 1 base st)
 obtain ⟨hz⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p I.iteratorTag 1 base st hi ctx (s ::ᵥ nil)
 obtain ⟨hp⟩ := Equations.projection p (I.iteratorTag+1) (0 : Fin 1) hb (s ::ᵥ nil)
 exact ⟨Logic.trans _ _ _ hz hp⟩

theorem successor {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (count s : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (iteratorCall I.iteratorTag (.succ count) s)
   (stepCall I.stepTag (iteratorCall I.iteratorTag count s)))) := by
 let base : Program 1 := .projection 0
 let st : Program 3 := HistoryRuleSuffix.applyOne step (.projection 1)
 have hi : (nodes p)[I.iteratorTag]? = some ⟨2, .recursion base st⟩ := I.hiterator
 have hs := Equations.recursionStepChild p I.iteratorTag base st hi
 obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p I.iteratorTag 1 base st hi ctx count (s ::ᵥ nil)
 let previous := iteratorCall I.iteratorTag count s
 let args := count ::ᵥ previous ::ᵥ s ::ᵥ nil
 have hprevious : Computes p [] (.projection (1 : Fin 3)) args previous := projection p [] args 1
 obtain ⟨hstep⟩ := unary p [] args step (.projection 1) previous (stepCall I.stepTag previous) hprevious
  (copies p [] step I.stepTag I.hstep (previous ::ᵥ nil)) (I.iteratorTag+GorbowPRChildTags.stepTag base) hs
 exact ⟨Hilbert.Local.finish (localTrans _ _ _ (.base hr) hstep)⟩

theorem substIterator {m n : Nat} (sub : Fin m → Term n) tag (count s : Term m) :
 substitute sub (iteratorCall tag count s) = iteratorCall tag (substitute sub count) (substitute sub s) := by
 simp only [iteratorCall,RawIteratedSucc.iteratorCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]

def template {ctx : Nat} (v q c a l r it : Nat) (s index fuel : Term ctx) : Formula (ctx+1) :=
 .imp (invariant v q c a l r (liftTerm index) (liftTerm fuel) (liftTerm s))
  (invariant v q c a l r (liftTerm index) (liftTerm fuel) (iteratorCall it (.var 0) (liftTerm s)))
theorem templateAt {ctx : Nat} v q c a l r it (s index fuel count : Term ctx) :
 GorbowStandardInstances.instantiate (template v q c a l r it s index fuel) count =
 .imp (invariant v q c a l r index fuel s)
  (invariant v q c a l r index fuel (iteratorCall it count s)) := by
 simp only [GorbowStandardInstances.instantiate,template,substituteFormula,substInvariant,substIterator,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem invariantIteration : ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (count s index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (invariant I.validatorTag I.qctag I.consTag I.appendTag I.leftTag I.rightTag index fuel s)
   (invariant I.validatorTag I.qctag I.consTag I.appendTag I.leftTag I.rightTag index fuel
    (iteratorCall I.iteratorTag count s)))) := by
 intro n p old a x I ctx count s index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let phi := template I.validatorTag I.qctag I.consTag I.appendTag I.leftTag I.rightTag I.iteratorTag s index fuel
 obtain ⟨hz⟩ := zero p old a x I s
 have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
  rw [show phi = template I.validatorTag I.qctag I.consTag I.appendTag I.leftTag I.rightTag I.iteratorTag s index fuel from rfl,templateAt]
  exact .mp (transport I.validatorTag I.qctag I.consTag I.appendTag I.leftTag I.rightTag index fuel s (iteratorCall I.iteratorTag .zero s))
   (Support.equalitySymmetry _ _ hz)
 let S := liftTerm s
 let N := liftTerm index
 let F := liftTerm fuel
 let j : Term (ctx+1) := .var 0
 let initial := invariant I.validatorTag I.qctag I.consTag I.appendTag I.leftTag I.rightTag N F S
 let previous := iteratorCall I.iteratorTag j S
 have hinit : Hilbert.Local T (ctx+1) [initial,phi] initial := .hypothesis List.mem_cons_self
 have hih : Hilbert.Local T (ctx+1) [initial,phi] phi := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hprev := Hilbert.Local.mp hih hinit
 obtain ⟨hpres⟩ := InvariantProof.internalPreservation p old a x I previous N F
 have hnext := Hilbert.Local.mp (.base hpres) hprev
 obtain ⟨hs⟩ := successor p old a x I j S
 have hout := Hilbert.Local.mp (.mp (.base (transport I.validatorTag I.qctag I.consTag I.appendTag I.leftTag I.rightTag N F
  (stepCall I.stepTag previous) (iteratorCall I.iteratorTag (.succ j) S))) (.base (Support.equalitySymmetry _ _ hs))) hnext
 have hstep : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simpa only [phi,template,GorbowStandardInduction.successorInstance,substituteFormula,substInvariant,substIterator,
   substitute,successorLift,Fin.cases_zero,S,N,F,j,initial,previous] using
   Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))
 have h := atTerm phi count (HistoryCodec.ArithmeticSupport.induction phi hb hstep)
 exact ⟨by simpa only [phi,templateAt] using h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestSuccIteration.IterationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestSuccIteration.IterationProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestSuccIteration.IterationProof.invariantIteration
