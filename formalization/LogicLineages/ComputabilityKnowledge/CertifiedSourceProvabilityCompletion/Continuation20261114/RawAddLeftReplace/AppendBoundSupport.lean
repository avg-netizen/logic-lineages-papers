module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.PairTailBoundProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.AppendBoundSupport
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryBounds HistoryBounds.SupportProof HistoryCancellation HistoryCancellation.MonotonicityProof
open HistoryLengthOffset HistoryLengthOffset.EquationsProof HistoryLengthOffset.SelectProof
open HistoryLengthOffset.OffsetSupportProof (substLength)
open HistoryAppend.PreserveSupportProof (substAppend)
open LiteralRawMP.DispatcherSupportProof

theorem consWeak {n ctx : Nat} (p : Program n) (tag : Nat)
 (hc : (nodes p)[tag]? = some ⟨2,HistoryCodec.cons⟩) (a b c : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (weakBound b c) (weakBound (HistoryLookup.consCall tag a b) (HistoryLookup.consCall tag a c)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let cp := tag+GorbowPRChildTags.argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0
 have hp := SixSol20261112.Fuel.Equations.argumentChild p tag .succ (fun _ : Fin 1 => HistoryCodec.pair) hc 0
 obtain ⟨hm⟩ := PairTailBoundProof.weakPair p cp hp a b c
 let H := weakBound b c
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hs⟩ := weakSuccessor T (HistoryDifference.pairCall cp a b) (HistoryDifference.pairCall cp a c)
 obtain ⟨hw⟩ := HistoryIteratorSuffix.SectorSplitProof.successorWeak T (HistoryDifference.pairCall cp a b) (.succ (HistoryDifference.pairCall cp a c))
 have hsucc := Hilbert.Local.mp (.base hw) (.mp (.base hs) (.mp (.base hm) hh))
 obtain ⟨hb⟩ := HistoryCodec.PairProof.internalCons n p tag hc ctx a b
 obtain ⟨hc'⟩ := HistoryCodec.PairProof.internalCons n p tag hc ctx a c
 have hright := Hilbert.Local.mp (.mp (.base (HistoryBounds.PairProof.weakTransport _ _ _)) (.base hc')) hsucc
 have hout := Hilbert.Local.mp (.mp (.base (weakChildTransport _ _ _)) (.base hb)) hright
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩

def property {ctx : Nat} (_ltag atag _rtag : Nat) (left right _index : Term ctx) : Formula ctx :=
 weakBound left (HistoryAppend.appendCall atag left right)
theorem substOffset {m n : Nat} (sub : Fin m → Term n) ltag atag rtag (left right index : Term m) :
 substituteFormula sub (property ltag atag rtag left right index) =
 property ltag atag rtag (substitute sub left) (substitute sub right) (substitute sub index) := by
 simp only [property,substWeak,substAppend]

theorem nilOffset {n ctx : Nat} (p : Program n) (ltag atag rtag : Nat)
 (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hr : (nodes p)[rtag]? = some ⟨2,HistoryLookup.drop⟩) (right index : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (property ltag atag rtag .zero right index)) := by
 exact ⟨HistoryCancellation.OrderSupportProof.weakZero _⟩

theorem consOffset {n ctx : Nat} (p : Program n) (ltag atag rtag ctag : Nat)
 (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hr : (nodes p)[rtag]? = some ⟨2,HistoryLookup.drop⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (head left right index : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (property ltag atag rtag left right index)
  (property ltag atag rtag (HistoryLookup.consCall ctag head left) right index))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let Q := property ltag atag rtag left right index
 have ih : Hilbert.Local T ctx [Q] Q := .hypothesis List.mem_cons_self
 obtain ⟨hm⟩ := consWeak p ctag hc head left (HistoryAppend.appendCall atag left right)
 obtain ⟨happ⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx head left right
 have hout := Hilbert.Local.mp (.mp (.base (HistoryBounds.PairProof.weakTransport _ _ _)) (.base happ)) (.mp (.base hm) ih)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩
def bounded {ctx : Nat} (ltag atag rtag : Nat) (count left right index : Term ctx) : Formula ctx :=
  .imp (.equal (lengthCall ltag left) count) (property ltag atag rtag left right index)
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
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.AppendBoundSupport
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.AppendBoundSupport
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.AppendBoundSupport.consWeak
