module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.BoundSupportProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.DropInductionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryBounds HistoryBounds.SupportProof

def bounded {ctx : Nat} (tag : Nat) (count lines : Term ctx) : Formula ctx :=
  .imp (weakBound lines count) (.equal (dropCall tag count lines) .zero)
def allBounded {ctx : Nat} (tag : Nat) (count : Term ctx) : Formula ctx :=
  .all (bounded tag (liftTerm count) (.var 0))
def stepGoal {ctx : Nat} (tag : Nat) (count lines : Term ctx) : Formula ctx :=
  .imp (allBounded tag count) (bounded tag (.succ count) lines)

theorem substDrop {m n : Nat} (sub : Fin m → Term n) tag (count lines : Term m) :
    substitute sub (dropCall tag count lines) = dropCall tag (substitute sub count) (substitute sub lines) := by
  simp only [dropCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
theorem substBounded {m n : Nat} (sub : Fin m → Term n) tag (count lines : Term m) :
    substituteFormula sub (bounded tag count lines) = bounded tag (substitute sub count) (substitute sub lines) := by
  simp only [bounded,substituteFormula,substWeak,substDrop,substitute]
theorem substAllBounded {m n : Nat} (sub : Fin m → Term n) tag (count : Term m) :
    substituteFormula sub (allBounded tag count) = allBounded tag (substitute sub count) := by
  simp only [allBounded,substituteFormula,substBounded,HistoryOrder.SupportProof.substituteLift,
    substitute,liftSubstitute,Fin.cases_zero]
theorem boundedAt {ctx : Nat} tag (count lines : Term ctx) :
    GorbowStandardInstances.instantiate (bounded tag (liftTerm count) (.var 0)) lines = bounded tag count lines := by
  simp only [GorbowStandardInstances.instantiate,substBounded,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
noncomputable def instanceRule {T : Sentence → Prop} {ctx : Nat} tag (count lines : Term ctx) :
    Derivation T (.imp (allBounded tag count) (bounded tag count lines)) := by
  have h := Derivation.logical (A := T) (.allInstantiate (bounded tag (liftTerm count) (.var 0)) lines)
  rwa [GorbowPACore.logicalFormula,boundedAt] at h

theorem base {n ctx : Nat} (p : Program n) (tag : Nat)
    (ht : (nodes p)[tag]? = some ⟨2,HistoryLookup.drop⟩) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (allBounded (ctx := ctx) tag .zero)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let line : Term (ctx+1) := .var 0
  let H := weakBound line .zero
  obtain ⟨hz⟩ := HistoryLookup.DropEquationsProof.dropZero p tag ht line
  obtain ⟨hb⟩ := BoundSupportProof.weakZero T line
  have hh : Hilbert.Local T (ctx+1) [H] H := .hypothesis List.mem_cons_self
  have hout := localTrans _ _ _ (.base hz) (.mp (.base hb) hh)
  exact ⟨.generalize (Hilbert.Local.finish (Hilbert.Local.discharge hout))⟩

theorem positiveStep {n ctx : Nat} (p : Program n) (tag : Nat)
    (ht : (nodes p)[tag]? = some ⟨2,HistoryLookup.drop⟩) (count code : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (stepGoal tag count (.succ code))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let I := allBounded tag count
  let H := weakBound (.succ code) (.succ count)
  let tt := HistoryLookup.DropEquationsProof.tailTag tag
  let tail := call tt (.succ code ::ᵥ nil)
  have htt := HistoryLookup.DropEquationsProof.tailInstalled p tag ht
  obtain ⟨hb⟩ := HistoryDecoderBounds.OuterRangeProof.internalPositiveTailBound n p tt htt ctx code
  obtain ⟨hc⟩ := BoundSupportProof.weakSuccessorCancel T code count
  obtain ⟨htrans⟩ := HistoryCancellation.TransitivityProof.weakTrans T tail code count
  have hh : Hilbert.Local T ctx [H,I] H := .hypothesis List.mem_cons_self
  have hi : Hilbert.Local T ctx [H,I] I := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  have htail : Hilbert.Local T ctx [H,I] (weakBound tail count) :=
    .mp (.mp (.base htrans) (.base hb)) (.mp (.base hc) hh)
  have hz : Hilbert.Local T ctx [H,I] (.equal (dropCall tag count tail) .zero) :=
    .mp (.mp (.base (instanceRule tag count tail)) hi) htail
  obtain ⟨hs⟩ := HistoryAppend.LookupShiftProof.dropShift p tag ht count (.succ code)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (localTrans _ _ _ (.base hs) hz)))⟩

theorem substStep {m n : Nat} (sub : Fin m → Term n) tag (count lines : Term m) :
    substituteFormula sub (stepGoal tag count lines) = stepGoal tag (substitute sub count) (substitute sub lines) := by
  simp only [stepGoal,substituteFormula,substAllBounded,substBounded,substitute]
theorem stepAt {ctx : Nat} tag (count lines : Term ctx) :
    GorbowStandardInstances.instantiate (stepGoal tag (liftTerm count) (.var 0)) lines = stepGoal tag count lines := by
  simp only [GorbowStandardInstances.instantiate,substStep,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
noncomputable def stepTransport {T : Sentence → Prop} {ctx : Nat} tag (count a b : Term ctx) :
    Derivation T (.imp (.equal a b) (.imp (stepGoal tag count a) (stepGoal tag count b))) := by
  have he := Derivation.logical (A := T) (.equalityReplace (stepGoal tag (liftTerm count) (.var 0)) a b)
  rwa [GorbowPACore.logicalFormula,stepAt,stepAt] at he

theorem stepAtLine {n ctx : Nat} (p : Program n) (tag : Nat)
    (ht : (nodes p)[tag]? = some ⟨2,HistoryLookup.drop⟩) (count lines : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (stepGoal tag count lines)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := stepGoal tag count lines
  let E := Formula.equal lines .zero
  obtain ⟨hz⟩ := HistoryLookup.DropProof.dropNil p tag ht (.succ count)
  have hn : Derivation T (stepGoal tag count .zero) := Hilbert.lift _ (Hilbert.lift _ hz)
  have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  have hzero : Derivation T (.imp E Q) := Hilbert.Local.finish (Hilbert.Local.discharge
    (.mp (.mp (.base (stepTransport tag count .zero lines)) (HistoryOrder.StepProof.localSym _ _ he)) (.base hn)))
  let H := HistoryOrder.SupportProof.predBody lines
  have hh : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm lines) (.succ (.var 0))) := .hypothesis List.mem_cons_self
  obtain ⟨hp⟩ := positiveStep p tag ht (liftTerm count) (.var (0 : Fin (ctx+1)))
  have hout : Hilbert.Local T (ctx+1) [H] (stepGoal tag (liftTerm count) (liftTerm lines)) :=
    .mp (.mp (.base (stepTransport tag (liftTerm count) _ _)) (HistoryOrder.StepProof.localSym _ _ hh)) (.base hp)
  have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
    simpa only [Q,GorbowPACore.weaken,substStep,liftTerm,renameTerm] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
  obtain ⟨hpos⟩ := HBQuantifier.existentialElimination T H Q ⟨hb⟩
  obtain ⟨hs⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T lines
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzero) hpos) hs⟩

theorem step {n ctx : Nat} (p : Program n) (tag : Nat)
    (ht : (nodes p)[tag]? = some ⟨2,HistoryLookup.drop⟩) (count : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (allBounded tag count) (allBounded tag (.succ count)))) := by
  obtain ⟨hs⟩ := stepAtLine p tag ht (liftTerm count) (.var (0 : Fin (ctx+1)))
  have hh : Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (GorbowPACore.weaken (allBounded tag count)) (bounded tag (liftTerm (.succ count)) (.var 0))) := by
    simpa only [stepGoal,GorbowPACore.weaken,substAllBounded,liftTerm,renameTerm,substitute] using hs
  exact ⟨HistoryIteratorSuffix.RelationProof.universalUnder (allBounded tag count) _ hh⟩

theorem internalDropExhaustion : Targets.InternalDropExhaustion := by
  intro n p tag ht ctx count lines
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := allBounded tag (.var (0 : Fin (ctx+1)))
  obtain ⟨hz⟩ := base (ctx := ctx) p tag ht
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    simpa only [phi,GorbowStandardInstances.instantiate,substAllBounded,substitute,Fin.cases_zero] using hz
  obtain ⟨hn⟩ := step p tag ht (.var (0 : Fin (ctx+1)))
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simpa only [phi,GorbowStandardInduction.successorInstance,substAllBounded,substitute,Fin.cases_zero] using hn
  have h := atTerm phi count (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  have hc : Derivation T (allBounded tag count) := by
    simpa only [phi,GorbowStandardInstances.instantiate,substAllBounded,substitute,Fin.cases_zero] using h
  exact ⟨.mp (instanceRule tag count lines) hc⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.DropInductionProof
