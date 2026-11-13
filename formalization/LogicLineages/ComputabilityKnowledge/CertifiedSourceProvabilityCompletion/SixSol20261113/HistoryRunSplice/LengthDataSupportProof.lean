module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.IdleProof

public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.LengthDataSupportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryLengthOffset HistoryLengthOffset.EquationsProof HistoryLengthOffset.SelectProof
open HistoryLengthOffset.OffsetSupportProof (substLength)
open HistoryAppend.PreserveSupportProof (substAppend)
open HistoryLookup.DropEquationsProof (dropCall substDrop)

/-- Internal structural data; the spare index parameter keeps induction uniform. -/
def property {ctx : Nat} (ltag atag dtag : Nat) (left right _index : Term ctx) : Formula ctx :=
  .conj (.equal (dropCall dtag (lengthCall ltag left) left) .zero)
    (.conj (HistoryBounds.weakBound (lengthCall ltag left) left)
      (.equal (lengthCall ltag (HistoryAppend.appendCall atag left right))
        (.add (lengthCall ltag left) (lengthCall ltag right))))
theorem substOffset {m n : Nat} (sub : Fin m → Term n) ltag atag rtag (left right index : Term m) :
    substituteFormula sub (property ltag atag rtag left right index)=
      property ltag atag rtag (substitute sub left) (substitute sub right) (substitute sub index) := by
  simp only [property,substituteFormula,substDrop,substLength,substAppend,HistoryBounds.SupportProof.substWeak,substitute]

noncomputable def lengthCongruence {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)} ltag (a b : Term ctx)
    (h : Hilbert.Local T ctx G (.equal a b)) : Hilbert.Local T ctx G (.equal (lengthCall ltag a) (lengthCall ltag b)) := by
  have he := localUnary (lengthCall ltag (.var 0)) a b h
  simpa only [substLength,substitute,Fin.cases_zero] using he
noncomputable def weakTransport {T : Sentence → Prop} {ctx : Nat} (a b code : Term ctx) :
    Derivation T (.imp (.equal a b) (.imp (HistoryBounds.weakBound a code) (HistoryBounds.weakBound b code))) := by
  have h := Derivation.logical (A := T) (.equalityReplace (HistoryBounds.weakBound (.var 0) (liftTerm code)) a b)
  simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,HistoryBounds.SupportProof.substWeak,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h

theorem nilOffset {n ctx : Nat} (p : Program n) (ltag atag rtag : Nat)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hr : (nodes p)[rtag]? = some ⟨2,HistoryLookup.drop⟩) (right index : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (property ltag atag rtag .zero right index)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  obtain ⟨hlen⟩ := internalLengthNil n p ltag hl ctx
  obtain ⟨happ⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx right
  obtain ⟨hdr⟩ := HistoryLookup.DropEquationsProof.dropZero p rtag hr (.zero : Term ctx)
  have hd := localTrans _ _ _ (countCongruence (T := T) (G := []) rtag _ .zero .zero .zero (.base hlen) (.base (.logical (.reflexive _)))) (.base hdr)
  have href := HistoryCancellation.OrderSupportProof.weakReflexive (T := T) (.zero : Term ctx)
  have hb : Hilbert.Local T ctx [] (HistoryBounds.weakBound (lengthCall ltag .zero) .zero) := Hilbert.Local.mp (.mp (.base (weakTransport .zero (lengthCall ltag .zero) (.zero : Term ctx)))
    (.base (Support.equalitySymmetry _ _ hlen))) (.base href)
  have hsum := localUnary (.add (.var 0) (liftTerm (lengthCall ltag right))) _ _ (Hilbert.Local.base (Gamma := []) hlen)
  simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hsum
  have hs := localTrans _ _ _ hsum (.base (zeroLeft (lengthCall ltag right)))
  have he := localTrans _ _ _ (lengthCongruence ltag _ _ (Hilbert.Local.base (Gamma := []) happ)) (HistoryOrder.StepProof.localSym _ _ hs)
  exact ⟨Hilbert.Local.finish (.mp (.mp (.base (.logical (.andIntro _ _))) hd)
    (.mp (.mp (.base (.logical (.andIntro _ _))) hb) he))⟩

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
  let code := HistoryLookup.consCall ctag head left
  let L := lengthCall ltag left
  have ih : Hilbert.Local T ctx [Q] Q := .hypothesis List.mem_cons_self
  have hd0 : Hilbert.Local T ctx [Q] (.equal (dropCall rtag L left) .zero) := .mp (.base (.logical (.andLeft _ _))) ih
  have hb0 : Hilbert.Local T ctx [Q] (HistoryBounds.weakBound L left) := .mp (.base (.logical (.andLeft _ _))) (.mp (.base (.logical (.andRight _ _))) ih)
  have he0 : Hilbert.Local T ctx [Q] (.equal (lengthCall ltag (HistoryAppend.appendCall atag left right)) (.add L (lengthCall ltag right))) :=
    .mp (.base (.logical (.andRight _ _))) (.mp (.base (.logical (.andRight _ _))) ih)
  obtain ⟨hlen⟩ := HistoryLengthOffset.ConsProof.internalLengthCons n p ltag ctag hl hc ctx head left
  obtain ⟨hdr⟩ := HistoryLookup.DropProof.dropCons p rtag ctag hr hc L head left
  have hd := localTrans _ _ _ (countCongruence rtag _ (.succ L) code code (Hilbert.Local.base (Gamma := [Q]) hlen) (.base (.logical (.reflexive code))))
    (localTrans _ _ _ (.base hdr) hd0)
  obtain ⟨hsucc⟩ := HistoryBounds.SupportProof.weakSuccessor T L left
  obtain ⟨hsuccWeak⟩ := HistoryIteratorSuffix.SectorSplitProof.successorWeak T L (.succ left)
  obtain ⟨hstrict⟩ := HistoryBounds.ConsProof.consSecondStrictBound n p ctag hc ctx head left
  obtain ⟨hsw⟩ := HistoryIteratorSuffix.SectorSplitProof.successorWeak T left code
  obtain ⟨htrans⟩ := HistoryCancellation.TransitivityProof.weakTrans T (.succ L) (.succ left) code
  have hb1 := Hilbert.Local.mp (.mp (.base htrans) (.mp (.base hsuccWeak) (.mp (.base hsucc) hb0))) (.mp (.base hsw) (.base hstrict))
  have hb := Hilbert.Local.mp (.mp (.base (weakTransport (.succ L) (lengthCall ltag code) code))
    (.base (Support.equalitySymmetry _ _ hlen))) hb1
  obtain ⟨happ⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx head left right
  obtain ⟨happLen⟩ := HistoryLengthOffset.ConsProof.internalLengthCons n p ltag ctag hl hc ctx head (HistoryAppend.appendCall atag left right)
  have hsum := localUnary (.add (.var 0) (liftTerm (lengthCall ltag right))) _ _ (Hilbert.Local.base (Gamma := [Q]) hlen)
  simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hsum
  have hs := localTrans _ _ _ hsum (.base (successorLeft L (lengthCall ltag right)))
  have he := localTrans _ _ _ (lengthCongruence ltag _ _ (Hilbert.Local.base (Gamma := [Q]) happ))
    (localTrans _ _ _ (.base happLen) (localTrans _ _ _ (localUnary (.succ (.var 0)) _ _ he0) (HistoryOrder.StepProof.localSym _ _ hs)))
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.mp (.base (.logical (.andIntro _ _))) hd)
    (.mp (.mp (.base (.logical (.andIntro _ _))) hb) he)))⟩

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
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.LengthDataSupportProof

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.LengthDataSupportProof
