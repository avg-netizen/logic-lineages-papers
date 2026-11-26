module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.ConsRunProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.PrefixSupportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryLengthOffset
open HistoryAppend.PreserveSupportProof (substAppend)
open HistoryLengthOffset.OffsetSupportProof (substLength)
open IdleProof (substRun)

def relation {ctx : Nat} (itag ltag atag ptag : Nat) (left right option out index fuel : Term ctx) : Formula ctx :=
  .imp (.equal (run itag ptag (lengthCall ltag left) option left index fuel) (state ptag out .zero))
    (.equal (run itag ptag (lengthCall ltag left) option (HistoryAppend.appendCall atag left right) index fuel)
      (state ptag out right))
theorem substState {m n : Nat} (sub : Fin m → Term n) ptag (option lines : Term m) :
    substitute sub (state ptag option lines)=state ptag (substitute sub option) (substitute sub lines) := by
  simp only [state,HistoryKernel.pairCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
theorem substRelation {m n : Nat} (sub : Fin m → Term n) itag ltag atag ptag (left right option out index fuel : Term m) :
    substituteFormula sub (relation itag ltag atag ptag left right option out index fuel)=
      relation itag ltag atag ptag (substitute sub left) (substitute sub right) (substitute sub option)
        (substitute sub out) (substitute sub index) (substitute sub fuel) := by
  simp only [relation,substituteFormula,substRun,substLength,substAppend,substState,substitute]
def oneOption {ctx : Nat} (itag ltag atag ptag : Nat) (left right option index fuel : Term ctx) : Formula ctx :=
  .all (relation itag ltag atag ptag (liftTerm left) (liftTerm right) (liftTerm option) (.var 0) (liftTerm index) (liftTerm fuel))
def property {ctx : Nat} (itag ltag atag ptag : Nat) (left right index fuel : Term ctx) : Formula ctx :=
  .all (oneOption itag ltag atag ptag (liftTerm left) (liftTerm right) (.var 0) (liftTerm index) (liftTerm fuel))
theorem substOne {m n : Nat} (sub : Fin m → Term n) itag ltag atag ptag (left right option index fuel : Term m) :
    substituteFormula sub (oneOption itag ltag atag ptag left right option index fuel)=
      oneOption itag ltag atag ptag (substitute sub left) (substitute sub right) (substitute sub option) (substitute sub index) (substitute sub fuel) := by
  simp only [oneOption,substituteFormula,substRelation,HistoryOrder.SupportProof.substituteLift,substitute,liftSubstitute,Fin.cases_zero]
theorem substProperty {m n : Nat} (sub : Fin m → Term n) itag ltag atag ptag (left right index fuel : Term m) :
    substituteFormula sub (property itag ltag atag ptag left right index fuel)=
      property itag ltag atag ptag (substitute sub left) (substitute sub right) (substitute sub index) (substitute sub fuel) := by
  simp only [property,substituteFormula,substOne,HistoryOrder.SupportProof.substituteLift,substitute,liftSubstitute,Fin.cases_zero]
noncomputable def propertyElim {T : Sentence → Prop} {ctx : Nat} (itag ltag atag ptag : Nat) (left right option out index fuel : Term ctx) :
    Derivation T (.imp (property itag ltag atag ptag left right index fuel)
      (relation itag ltag atag ptag left right option out index fuel)) := by
  have ho := Derivation.logical (A := T) (.allInstantiate
    (oneOption itag ltag atag ptag (liftTerm left) (liftTerm right) (.var 0) (liftTerm index) (liftTerm fuel)) option)
  have hr := Derivation.logical (A := T) (.allInstantiate
    (relation itag ltag atag ptag (liftTerm left) (liftTerm right) (liftTerm option) (.var 0) (liftTerm index) (liftTerm fuel)) out)
  simp only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substOne,substRelation,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at ho hr
  exact Hilbert.compose hr ho

theorem nilRelation {n ctx : Nat} (p : Program n) (itag ltag atag ptag : Nat) (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (right option out index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (relation itag ltag atag ptag .zero right option out index fuel)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let H := Formula.equal (run itag ptag (lengthCall ltag .zero) option .zero index fuel) (state ptag out .zero)
  have h : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
  obtain ⟨hz⟩ := ConsRunProof.nilLength p itag ltag ptag v l a x hi hl option (.zero : Term ctx) index fuel
  have he := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (.base hz)) h
  obtain ⟨hinj⟩ := HistoryCancellation.InjectivityProof.pairInjective n p ptag hp ctx option .zero out .zero
  have hop : Hilbert.Local T ctx [H] (.equal option out) := .mp (.base (.logical (.andLeft _ _))) (.mp (.base hinj) he)
  have hstate := HistoryIteratorSuffix.StepSuffixProof.pairCongruence ptag option right out right hop (.base (.logical (.reflexive right)))
  obtain ⟨happ⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx right
  obtain ⟨hrun⟩ := ConsRunProof.nilLength p itag ltag ptag v l a x hi hl option (HistoryAppend.appendCall atag .zero right) index fuel
  have hrest := HistoryIteratorSuffix.StepSuffixProof.pairCongruence ptag option _ option right (.base (.logical (.reflexive option))) (Hilbert.Local.base (Gamma := [H]) happ)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ (.base hrun) (localTrans _ _ _ hrest hstate)))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.PrefixSupportProof

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.PrefixSupportProof
