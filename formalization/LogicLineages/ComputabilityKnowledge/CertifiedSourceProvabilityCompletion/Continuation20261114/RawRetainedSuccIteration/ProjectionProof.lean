module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccIteration.IterationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccIteration.ProjectionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open RawAdditionIteration (binaryCall successorPrefix)
theorem prefixZero {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (t : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (binaryCall I.prefixTag .zero t) t)) := by
 let b : Program 1 := .projection 0
 let st : Program 3 := RawAddSucc.successorRaw (.projection 1)
 have hb := GorbowPRSubtree.Proof.lookupTransport n p I.prefixTag ⟨2,successorPrefix⟩ 1 ⟨1,b⟩ I.hprefix
  (GorbowPRChildTags.Proof.recursionBase 1 b st)
 obtain ⟨hz⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p I.prefixTag 1 b st I.hprefix ctx (t ::ᵥ nil)
 obtain ⟨hp⟩ := SixSol20261112.Fuel.Equations.projection p (I.prefixTag+1) (0 : Fin 1) hb (t ::ᵥ nil)
 exact ⟨Logic.trans _ _ _ hz hp⟩

theorem prefixSuccessor {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (count t : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (binaryCall I.prefixTag (.succ count) t)
   (RawAdditionComputation.succRaw I.ctag (binaryCall I.prefixTag count t)))) := by
 let b : Program 1 := .projection 0
 let st : Program 3 := RawAddSucc.successorRaw (.projection 1)
 have hs := SixSol20261112.Fuel.Equations.recursionStepChild p I.prefixTag b st I.hprefix
 obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p I.prefixTag 1 b st I.hprefix ctx count (t ::ᵥ nil)
 let previous := binaryCall I.prefixTag count t
 let args := count ::ᵥ previous ::ᵥ t ::ᵥ nil
 obtain ⟨he⟩ := binary p [] args HistoryCodec.cons _ _ _ _ _ (constantValue p [] args 2)
  (projection p [] args 1) (copies p [] HistoryCodec.cons I.ctag I.hc _)
  (I.prefixTag+GorbowPRChildTags.stepTag b) hs
 exact ⟨Hilbert.Local.finish (localTrans _ _ _ (.base hr) he)⟩

theorem stepProjections {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (s : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (first I.leftTag (stepCall I.stepTag s)) (RawSuccReplace.succValue I.ctag (first I.leftTag s)))) ∧
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (second I.leftTag I.rightTag (stepCall I.stepTag s)) (RawSuccReplace.succValue I.ctag (second I.leftTag I.rightTag s)))) := by
 obtain ⟨hr⟩ := InvariantProof.reconstructState p old a x I s
 obtain ⟨hc⟩ := StepProof.internalStep n p old a x I ctx (first I.leftTag s) (second I.leftTag I.rightTag s) (third I.rightTag s)
 have he := Logic.trans _ _ _ (HistoryLookup.DestructorProof.unaryCallCongruence I.stepTag _ _ (Support.equalitySymmetry _ _ hr)) hc
 obtain ⟨⟨hd1⟩,⟨hd2⟩,_⟩ := InvariantProof.decodeState p old a x I
  (RawSuccReplace.succValue I.ctag (first I.leftTag s)) (RawSuccReplace.succValue I.ctag (second I.leftTag I.rightTag s))
  (RawSuccCongruence.certificate I.mpTag I.replaceTag I.reflexivityTag I.ctag I.atag (first I.leftTag s) (second I.leftTag I.rightTag s) (third I.rightTag s))
 exact ⟨⟨Logic.trans _ _ _ (HistoryLookup.DestructorProof.unaryCallCongruence I.leftTag _ _ he) hd1⟩,
  ⟨Logic.trans _ _ _ (HistoryLookup.DestructorProof.unaryCallCongruence I.leftTag _ _
   (HistoryLookup.DestructorProof.unaryCallCongruence I.rightTag _ _ he)) hd2⟩⟩

def property {ctx : Nat} (l r pref it : Nat) (count s : Term ctx) : Formula ctx :=
 .conj (.equal (first l (iteratorCall it count s)) (binaryCall pref count (first l s)))
  (.equal (second l r (iteratorCall it count s)) (binaryCall pref count (second l r s)))
theorem substProperty {m n : Nat} (sub : Fin m → Term n) l r pref it (count s : Term m) :
 substituteFormula sub (property l r pref it count s) = property l r pref it (substitute sub count) (substitute sub s) := by
 simp only [property,first,second,iteratorCall,RawIteratedSucc.first,RawIteratedSucc.second,RawIteratedSucc.iteratorCall,
  binaryCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substituteFormula,substitute]
def template {ctx : Nat} (l r pref it : Nat) (s : Term ctx) : Formula (ctx+1) :=
 property l r pref it (.var 0) (liftTerm s)
theorem templateAt {ctx : Nat} l r pref it (s count : Term ctx) :
 GorbowStandardInstances.instantiate (template l r pref it s) count = property l r pref it count s := by
 simp only [GorbowStandardInstances.instantiate,template,substProperty,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem projections {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (count s : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (property I.leftTag I.rightTag I.prefixTag I.iteratorTag count s)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let phi := template I.leftTag I.rightTag I.prefixTag I.iteratorTag s
 obtain ⟨hz⟩ := IterationProof.zero p old a x I s
 obtain ⟨hp1⟩ := prefixZero p old a x I (first I.leftTag s)
 obtain ⟨hp2⟩ := prefixZero p old a x I (second I.leftTag I.rightTag s)
 have h1 := Logic.trans _ _ _ (HistoryLookup.DestructorProof.unaryCallCongruence I.leftTag _ _ hz) (Support.equalitySymmetry _ _ hp1)
 have h2 := Logic.trans _ _ _ (HistoryLookup.DestructorProof.unaryCallCongruence I.leftTag _ _
  (HistoryLookup.DestructorProof.unaryCallCongruence I.rightTag _ _ hz)) (Support.equalitySymmetry _ _ hp2)
 have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
  rw [show phi = template I.leftTag I.rightTag I.prefixTag I.iteratorTag s from rfl,templateAt]
  exact .mp (.mp (.logical (.andIntro _ _)) h1) h2
 let S := liftTerm s
 let j : Term (ctx+1) := .var 0
 let previous := iteratorCall I.iteratorTag j S
 have hih : Hilbert.Local T (ctx+1) [phi] phi := .hypothesis List.mem_cons_self
 have hi1 := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hih
 have hi2 := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hih
 obtain ⟨hs⟩ := IterationProof.successor p old a x I j S
 obtain ⟨⟨hsp1⟩,⟨hsp2⟩⟩ := stepProjections p old a x I previous
 obtain ⟨hpp1⟩ := prefixSuccessor p old a x I j (first I.leftTag S)
 obtain ⟨hpp2⟩ := prefixSuccessor p old a x I j (second I.leftTag I.rightTag S)
 have hc1 := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := [phi]) I.ctag
  (Term.numeral 2) _ (Term.numeral 2) _ (.base (.logical (.reflexive _))) hi1
 have hc2 := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := [phi]) I.ctag
  (Term.numeral 2) _ (Term.numeral 2) _ (.base (.logical (.reflexive _))) hi2
 have hn1 := localTrans _ _ _ (.base (HistoryLookup.DestructorProof.unaryCallCongruence I.leftTag _ _ hs))
  (localTrans _ _ _ (.base hsp1) (localTrans _ _ _ hc1 (.base (Support.equalitySymmetry _ _ hpp1))))
 have hn2 := localTrans _ _ _ (.base (HistoryLookup.DestructorProof.unaryCallCongruence I.leftTag _ _
  (HistoryLookup.DestructorProof.unaryCallCongruence I.rightTag _ _ hs)))
  (localTrans _ _ _ (.base hsp2) (localTrans _ _ _ hc2 (.base (Support.equalitySymmetry _ _ hpp2))))
 have hout := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hn1) hn2
 have houtTyped : Hilbert.Local T (ctx+1) [phi]
  (property I.leftTag I.rightTag I.prefixTag I.iteratorTag (.succ j) S) := hout
 have hstep : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simpa only [phi,template,GorbowStandardInduction.successorInstance,substProperty,substitute,successorLift,Fin.cases_zero,S,j,previous] using
   Hilbert.Local.finish (Hilbert.Local.discharge houtTyped)
 have h := atTerm phi count (HistoryCodec.ArithmeticSupport.induction phi hb hstep)
 exact ⟨by simpa only [phi,templateAt] using h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccIteration.ProjectionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccIteration.ProjectionProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccIteration.ProjectionProof.stepProjections
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccIteration.ProjectionProof.projections
