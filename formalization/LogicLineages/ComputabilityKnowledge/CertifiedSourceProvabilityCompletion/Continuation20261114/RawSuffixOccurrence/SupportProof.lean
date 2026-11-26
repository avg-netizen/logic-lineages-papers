module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixOccurrence.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixOccurrence.SupportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryLengthOffset HistoryLengthOffset.EquationsProof HistoryLengthOffset.SelectProof
open HistoryLengthOffset.OffsetSupportProof (substLength)
open HistoryAppend.PreserveSupportProof (substAppend)
open HistoryLookup.DropEquationsProof (dropCall substDrop)
def property {ctx : Nat} (ltag atag rtag : Nat) (left right _index : Term ctx) : Formula ctx :=
 .equal (dropCall rtag (lengthCall ltag left) (HistoryAppend.appendCall atag left right)) right
theorem substOffset {m n : Nat} (sub : Fin m → Term n) ltag atag rtag (left right index : Term m) :
 substituteFormula sub (property ltag atag rtag left right index) =
 property ltag atag rtag (substitute sub left) (substitute sub right) (substitute sub index) := by
 simp only [property,substituteFormula,substDrop,substLength,substAppend]

theorem nilOffset {n ctx : Nat} (p : Program n) (ltag atag rtag : Nat)
 (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hr : (nodes p)[rtag]? = some ⟨2,HistoryLookup.drop⟩) (right index : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (property ltag atag rtag .zero right index)) := by
 obtain ⟨hlen⟩ := internalLengthNil n p ltag hl ctx
 obtain ⟨happ⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx right
 obtain ⟨hdr⟩ := HistoryLookup.DropEquationsProof.dropZero p rtag hr right
 have h := countCongruence (T := GorbowPRNumeralCalculation.Theory p) (G := []) rtag _ .zero _ right (.base hlen) (.base happ)
 exact ⟨Hilbert.Local.finish (localTrans _ _ _ h (.base hdr))⟩

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
 obtain ⟨hlen⟩ := HistoryLengthOffset.ConsProof.internalLengthCons n p ltag ctag hl hc ctx head left
 obtain ⟨happ⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx head left right
 obtain ⟨hdr⟩ := HistoryLookup.DropProof.dropCons p rtag ctag hr hc (lengthCall ltag left) head (HistoryAppend.appendCall atag left right)
 have h := countCongruence (T := T) (G := [Q]) rtag _ _ _ _ (.base hlen) (.base happ)
 have hout := localTrans _ _ _ h (localTrans _ _ _ (.base hdr) ih)
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
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixOccurrence.SupportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixOccurrence.SupportProof
