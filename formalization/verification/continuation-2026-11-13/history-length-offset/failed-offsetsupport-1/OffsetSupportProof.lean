module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.ConsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.OffsetSupportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport EquationsProof SelectProof
open HistoryAppend.PreserveSupportProof (substAppend)
open HistoryAppend.PositiveProof (substLookup)

theorem substLength {m n : Nat} (sub : Fin m → Term n) tag (code : Term m) :
    substitute sub (lengthCall tag code)=lengthCall tag (substitute sub code) := by
  simp only [lengthCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
theorem substOffset {m n : Nat} (sub : Fin m → Term n) ltag atag rtag (left right index : Term m) :
    substituteFormula sub (rightOffset ltag atag rtag left right index)=
      rightOffset ltag atag rtag (substitute sub left) (substitute sub right) (substitute sub index) := by
  simp only [rightOffset,substituteFormula,substLookup,substAppend,substLength,substitute]

theorem nilOffset {n ctx : Nat} (p : Program n) ltag atag rtag
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) (right index : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (rightOffset ltag atag rtag .zero right index)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  obtain ⟨hlen⟩ := internalLengthNil n p ltag hl ctx
  obtain ⟨happ⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx right
  have hsum := localUnary (GorbowSyntax.Term.add (.var 0) (liftTerm index)) _ _ (Hilbert.Local.base (Gamma := []) hlen)
  simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hsum
  have hidx := localTrans _ _ _ hsum (.base (zeroLeft index))
  exact ⟨Hilbert.Local.finish (countCongruence (T := T) rtag _ index _ right hidx (.base happ))⟩

theorem consOffset {n ctx : Nat} (p : Program n) ltag atag rtag ctag
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hr : (nodes p)[rtag]? = some ⟨2,HistoryLookup.lookup⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (head left right index : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (rightOffset ltag atag rtag left right index)
        (rightOffset ltag atag rtag (HistoryLookup.consCall ctag head left) right index))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := rightOffset ltag atag rtag left right index
  have ih : Hilbert.Local T ctx [Q] Q := .hypothesis List.mem_cons_self
  obtain ⟨hlen⟩ := ConsProof.internalLengthCons n p ltag ctag hl hc ctx head left
  obtain ⟨happ⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx head left right
  have hsum := localUnary (GorbowSyntax.Term.add (.var 0) (liftTerm index)) _ _ (Hilbert.Local.base (Gamma := [Q]) hlen)
  simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hsum
  have hidx := localTrans _ _ _ hsum (.base (successorLeft (lengthCall ltag left) index))
  have hargs := countCongruence rtag _ _ _ _ hidx (.base happ)
  obtain ⟨hlookup⟩ := HistoryLookup.LookupProof.internalLookupSuccessorCons n p rtag ctag hr hc ctx
    (.add (lengthCall ltag left) index) head (HistoryAppend.appendCall atag left right)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ hargs (localTrans _ _ _ (.base hlookup) ih)))⟩

def bounded {ctx : Nat} (ltag atag rtag : Nat) (count left right index : Term ctx) : Formula ctx :=
  .imp (.equal (lengthCall ltag left) count) (rightOffset ltag atag rtag left right index)
def allBounded {ctx : Nat} (ltag atag rtag : Nat) (count right index : Term ctx) : Formula ctx :=
  .all (bounded ltag atag rtag (liftTerm count) (.var 0) (liftTerm right) (liftTerm index))
theorem substBounded {m n : Nat} (sub : Fin m → Term n) ltag atag rtag (count left right index : Term m) :
    substituteFormula sub (bounded ltag atag rtag count left right index)=
      bounded ltag atag rtag (substitute sub count) (substitute sub left) (substitute sub right) (substitute sub index) := by
  simp only [bounded,substituteFormula,substLength,substOffset]
theorem substAll {m n : Nat} (sub : Fin m → Term n) ltag atag rtag (count right index : Term m) :
    substituteFormula sub (allBounded ltag atag rtag count right index)=
      allBounded ltag atag rtag (substitute sub count) (substitute sub right) (substitute sub index) := by
  simp only [allBounded,substituteFormula,substBounded,HistoryOrder.SupportProof.substituteLift,
    substitute,liftSubstitute,Fin.cases_zero]
theorem allAt {ctx : Nat} ltag atag rtag (count left right index : Term ctx) :
    GorbowStandardInstances.instantiate
      (bounded ltag atag rtag (liftTerm count) (.var 0) (liftTerm right) (liftTerm index)) left =
      bounded ltag atag rtag count left right index := by
  simp only [GorbowStandardInstances.instantiate,substBounded,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
noncomputable def allElim {T : Sentence → Prop} {ctx : Nat} ltag atag rtag (count left right index : Term ctx) :
    Derivation T (.imp (allBounded ltag atag rtag count right index) (bounded ltag atag rtag count left right index)) := by
  have h := Derivation.logical (A := T) (.allInstantiate
    (bounded ltag atag rtag (liftTerm count) (.var 0) (liftTerm right) (liftTerm index)) left)
  rwa [GorbowPACore.logicalFormula,allAt] at h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.OffsetSupportProof
