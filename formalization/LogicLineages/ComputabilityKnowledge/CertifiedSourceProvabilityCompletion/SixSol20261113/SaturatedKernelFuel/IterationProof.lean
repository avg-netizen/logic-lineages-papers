module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.SimulationCasesProof

public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.IterationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel SixSol20261112.HistoryMachine NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryKernel RelationProof SimulationProof

theorem oldAt {ctx : Nat} ptag (old new : Term ctx) :
    GorbowStandardInstances.instantiate (relation ptag (.var 0) (liftTerm new)) old =
      relation ptag old new := by
  simp only [GorbowStandardInstances.instantiate,substRelation,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
theorem newAt {ctx : Nat} ptag (old new : Term ctx) :
    GorbowStandardInstances.instantiate (relation ptag (liftTerm old) (.var 0)) new =
      relation ptag old new := by
  simp only [GorbowStandardInstances.instantiate,substRelation,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

noncomputable def relationOld {T : Sentence → Prop} {ctx : Nat} ptag (old old' new : Term ctx) :
    Derivation T (.imp (.equal old old') (.imp (relation ptag old new) (relation ptag old' new))) := by
  have h := Derivation.logical (A := T) (.equalityReplace (relation ptag (.var 0) (liftTerm new)) old old')
  rwa [GorbowPACore.logicalFormula,oldAt,oldAt] at h
noncomputable def relationNew {T : Sentence → Prop} {ctx : Nat} ptag (old new new' : Term ctx) :
    Derivation T (.imp (.equal new new') (.imp (relation ptag old new) (relation ptag old new'))) := by
  have h := Derivation.logical (A := T) (.equalityReplace (relation ptag (liftTerm old) (.var 0)) new new')
  rwa [GorbowPACore.logicalFormula,newAt,newAt] at h

noncomputable def relationReverse {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)} ptag
    (old new old' new' : Term ctx) (ho : Derivation T (.equal old old')) (hn : Derivation T (.equal new new'))
    (hr : Hilbert.Local T ctx G (relation ptag old' new')) :
    Hilbert.Local T ctx G (relation ptag old new) :=
  .mp (.mp (.base (relationNew ptag old new' new)) (.base (Support.equalitySymmetry _ _ hn)))
    (.mp (.mp (.base (relationOld ptag old' old new')) (.base (Support.equalitySymmetry _ _ ho))) hr)

theorem substIteration {m n : Nat} (sub : Fin m → Term n) itag (count state index fuel : Term m) :
 substitute sub (iterationCall itag count state index fuel) =
 iterationCall itag (substitute sub count) (substitute sub state) (substitute sub index) (substitute sub fuel) :=
 HistoryIteratorSuffix.IterationProof.substIteration sub itag count state index fuel

def template {ctx : Nat} (itag ptag : Nat) (state index s t : Term ctx) : Formula (ctx+1) :=
 .imp (orderGuard (liftTerm s) (liftTerm t))
  (relation ptag (iterationCall itag (.var 0) (liftTerm state) (liftTerm index) (liftTerm s))
   (iterationCall itag (.var 0) (liftTerm state) (liftTerm index) (liftTerm t)))
theorem templateAt {ctx : Nat} itag ptag (state index s t count : Term ctx) :
 GorbowStandardInstances.instantiate (template itag ptag state index s t) count =
 .imp (orderGuard s t) (relation ptag (iterationCall itag count state index s)
  (iterationCall itag count state index t)) := by
 simp only [GorbowStandardInstances.instantiate,template,substituteFormula,substOrder,substRelation,substIteration,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

/-- Fuel order is INSIDE the induction formula. No generalization rule is
applied to an undischarged local assumption, including the order assumption. -/
theorem iterateRelation {n ctx : Nat} (p : Program n) (itag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
 (ht : (nodes p)[itag]? = some ⟨4,iterator (kernel v l a (SaturatedAxiomLeaf.saturated x))⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (state index s t count : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (orderGuard s t) (relation ptag (iterationCall itag count state index s)
   (iterationCall itag count state index t)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let k := kernel v l a (SaturatedAxiomLeaf.saturated x)
 let phi := template itag ptag state index s t
 obtain ⟨hr⟩ := RelationProof.reflexive T ptag state
 obtain ⟨hoz⟩ := HistoryMachine.Equations.zero p itag k ht state index s
 obtain ⟨hnz⟩ := HistoryMachine.Equations.zero p itag k ht state index t
 have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
  rw [show phi = template itag ptag state index s t from rfl,templateAt]
  exact Hilbert.lift _ (Hilbert.Local.finish (relationReverse ptag _ _ _ _ hoz hnz (.base hr)))
 let O := iterationCall itag (.var (0 : Fin (ctx+1))) (liftTerm state) (liftTerm index) (liftTerm s)
 let N := iterationCall itag (.var (0 : Fin (ctx+1))) (liftTerm state) (liftTerm index) (liftTerm t)
 let F := orderGuard (liftTerm s) (liftTerm t)
 have hk := Equations.functionChild p (itag+stepTag iterationBase) k iterationArguments
  (Equations.recursionStepChild p itag iterationBase (iterationStep k) ht)
 obtain ⟨hstep⟩ := SimulationCasesProof.kernelPreserves p (itag+stepTag iterationBase+1) ptag ctag v l a x hk hp hc
  O N (liftTerm index) (liftTerm s) (liftTerm t)
 have ih : Hilbert.Local T (ctx+1) [F,phi] phi := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hf : Hilbert.Local T (ctx+1) [F,phi] F := .hypothesis List.mem_cons_self
 have hr' : Hilbert.Local T (ctx+1) [F,phi] (relation ptag O N) := .mp ih hf
 have hpair : Hilbert.Local T (ctx+1) [F,phi] (premise ptag O N (liftTerm s) (liftTerm t)) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hf) hr'
 have next := Hilbert.Local.mp (.base hstep) hpair
 obtain ⟨hos⟩ := HistoryMachine.Equations.successor p itag k ht (.var (0 : Fin (ctx+1)))
  (liftTerm state) (liftTerm index) (liftTerm s)
 obtain ⟨hns⟩ := HistoryMachine.Equations.successor p itag k ht (.var (0 : Fin (ctx+1)))
  (liftTerm state) (liftTerm index) (liftTerm t)
 have hout := relationReverse ptag _ _ _ _ hos hns next
 have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simpa only [phi,template,F,O,N,GorbowStandardInduction.successorInstance,substituteFormula,substOrder,substRelation,substIteration,
   substitute,successorLift,Fin.cases_zero] using Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))
 have h := atTerm phi count (HistoryCodec.ArithmeticSupport.induction phi hb hs)
 exact ⟨by simpa only [phi,templateAt] using h⟩

theorem internalIterator : Targets.InternalIterator := by
 intro v l a x n p itag ptag ctag ht hp hc ctx count index s t h lines out rest
 let T := GorbowPRNumeralCalculation.Theory p
 let state := pairCall ptag (.succ h) lines
 let O := iterationCall itag count state index s
 let N := iterationCall itag count state index t
 obtain ⟨hr⟩ := iterateRelation p itag ptag ctag v l a x ht hp hc state index s t count
 have ho : Hilbert.Local T ctx [orderGuard s t] (orderGuard s t) := .hypothesis List.mem_cons_self
 have hb : Hilbert.Local T ctx [orderGuard s t] (body ptag O N out rest) :=
  .mp (.base (instanceRule ptag O N out rest)) (.mp (.base hr) ho)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hb)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.IterationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.IterationProof
