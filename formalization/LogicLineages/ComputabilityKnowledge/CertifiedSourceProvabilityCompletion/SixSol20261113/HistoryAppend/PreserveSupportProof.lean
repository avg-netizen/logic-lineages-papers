module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.PositiveLookupProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.PreserveSupportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open TableLookupProof TableEquationsProof AppendEquationsProof ValueEquationsProof PositiveProof

def preserve {ctx : Nat} (atag ltag : Nat) (index left right entry : Term ctx) : Formula ctx :=
  .imp (.equal (HistoryLookup.lookupCall ltag index left) (.succ entry))
    (.equal (HistoryLookup.lookupCall ltag index (appendCall atag left right)) (.succ entry))

def allPreserve {ctx : Nat} (atag ltag : Nat) (index right entry : Term ctx) : Formula ctx :=
  .all (preserve atag ltag (liftTerm index) (.var 0) (liftTerm right) (liftTerm entry))

theorem substAppend {m n : Nat} (sub : Fin m → Term n) tag (left right : Term m) :
    substitute sub (appendCall tag left right) = appendCall tag (substitute sub left) (substitute sub right) := by
  simp only [appendCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]

theorem substPreserve {m n : Nat} (sub : Fin m → Term n) atag ltag (index left right entry : Term m) :
    substituteFormula sub (preserve atag ltag index left right entry) =
      preserve atag ltag (substitute sub index) (substitute sub left) (substitute sub right) (substitute sub entry) := by
  simp only [preserve,substituteFormula,substLookup,substAppend,substitute]

theorem substAll {m n : Nat} (sub : Fin m → Term n) atag ltag (index right entry : Term m) :
    substituteFormula sub (allPreserve atag ltag index right entry) =
      allPreserve atag ltag (substitute sub index) (substitute sub right) (substitute sub entry) := by
  simp only [allPreserve,substituteFormula,substPreserve,HistoryOrder.SupportProof.substituteLift,
    substitute,liftSubstitute,Fin.cases_zero]

theorem allAt {ctx : Nat} atag ltag (index left right entry : Term ctx) :
    GorbowStandardInstances.instantiate
      (preserve atag ltag (liftTerm index) (.var 0) (liftTerm right) (liftTerm entry)) left =
      preserve atag ltag index left right entry := by
  simp only [GorbowStandardInstances.instantiate,substPreserve,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

def allElim {T : Sentence → Prop} {ctx : Nat} atag ltag (index left right entry : Term ctx) :
    Derivation T (.imp (allPreserve atag ltag index right entry) (preserve atag ltag index left right entry)) := by
  have h := Derivation.logical (A := T) (.allInstantiate
    (preserve atag ltag (liftTerm index) (.var 0) (liftTerm right) (liftTerm entry)) left)
  rwa [GorbowPACore.logicalFormula,allAt] at h

theorem weakenAll {ctx : Nat} atag ltag (index right entry : Term ctx) :
    GorbowPACore.weaken (allPreserve atag ltag index right entry) =
      allPreserve atag ltag (liftTerm index) (liftTerm right) (liftTerm entry) := by
  rw [GorbowPACore.weaken,substAll]
  rfl

theorem nilPreserve {n ctx : Nat} (p : Program n) atag ltag
    (hl : (nodes p)[ltag]? = some ⟨2,HistoryLookup.lookup⟩) (index right entry : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (preserve atag ltag index .zero right entry)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let E := Formula.equal (HistoryLookup.lookupCall ltag index .zero) (.succ entry)
  obtain ⟨hz⟩ := HistoryLookup.LookupProof.internalLookupNil n p ltag hl ctx index
  have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  have hbad := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ he) (.base hz)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
    (Hilbert.Local.explosion _ hbad (.base (.arithmetic (.succNotZero entry)))))⟩

theorem positiveZeroPreserve {n ctx : Nat} (p : Program n) atag ltag
    (ha : (nodes p)[atag]? = some ⟨2,append⟩)
    (hl : (nodes p)[ltag]? = some ⟨2,HistoryLookup.lookup⟩) (count right entry : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (preserve atag ltag .zero (.succ count) right entry)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let E := Formula.equal (HistoryLookup.lookupCall ltag .zero (.succ count)) (.succ entry)
  obtain ⟨h⟩ := PositiveLookupProof.zeroAppendPositive p atag ltag ha hl count right
  have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ (.base h) he))⟩

theorem positiveSuccessorPreserve {n ctx : Nat} (p : Program n) atag ltag
    (ha : (nodes p)[atag]? = some ⟨2,append⟩)
    (hl : (nodes p)[ltag]? = some ⟨2,HistoryLookup.lookup⟩) (index count right entry : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (allPreserve atag ltag index right entry) (preserve atag ltag (.succ index) (.succ count) right entry))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let P := allPreserve atag ltag index right entry
  let E := Formula.equal (HistoryLookup.lookupCall ltag (.succ index) (.succ count)) (.succ entry)
  let child := call (inputTailTag atag) (.succ count ::ᵥ nil)
  have hv := valueInstalled p (tableTag atag) (tableInstalled p atag ha)
  obtain ⟨hc,hh,ht,hd,href,hp⟩ := valueNodes p (valueAt atag) hv
  obtain ⟨hsource⟩ := LookupShiftProof.lookupShift p ltag (inputTailTag atag) hl ht index (.succ count)
  obtain ⟨houtput⟩ := PositiveLookupProof.successorAppendPositive p atag ltag ha hl index count right
  have hih : Hilbert.Local T ctx [E,P] P := .hypothesis (by simp)
  have he : Hilbert.Local T ctx [E,P] E := .hypothesis List.mem_cons_self
  have hchild := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hsource)) he
  have hi := Hilbert.Local.mp (.base (allElim atag ltag index child right entry)) hih
  have hout := localTrans _ _ _ (.base houtput) (.mp hi hchild)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.PreserveSupportProof
