module

public import LogicLineages.NativeModule.PersistentMarking.NativeTowerCodeTargets
import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalExponentialTypingProof
import LogicLineages.NativeModule.PersistentMarking.NumberedWindowOrdinaryDomainProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeTowerCode
open Spine NativeReduction NativeIndexedCarrierTargets NativeIteratorTargets
open NativeIteratorStrictTargets NativeTowerTargets NativeTowerSequenceTargets
open NativeOrdinalRealizationTargets NumberedWindowSyntax NumberedWindowOrdinaryTranslation
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticTyCode

/-! Primitive recursiveness uses only numerical constructor programs. -/

section Programs
variable {A : Type} [Primcodable A]

private theorem pairP {a b : A → Nat} (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => pairCode (a x) (b x)) :=
  Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.nat_add.comp ha hb) (Primrec.nat_add.comp ha hb)) ha

private theorem consP {a b : A → Nat} (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => consCode (a x) (b x)) :=
  Primrec.succ.comp (pairP ha hb)

private theorem node2P (tag : Nat) {a b : A → Nat} (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => node2Code tag (a x) (b x)) :=
  consP (Primrec.const tag) (consP ha (consP hb (Primrec.const 0)))

private theorem arrowP {a b : A → Nat} (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => arrowCode (a x) (b x)) := consP ha hb

private theorem boundP {a i : A → Nat} (ha : Primrec a) (hi : Primrec i) :
    Primrec (fun x => boundCode (a x) (i x)) := node2P 1 ha hi

private theorem lamP {a q : A → Nat} (ha : Primrec a) (hq : Primrec q) :
    Primrec (fun x => lamCode (a x) (q x)) := node2P 2 ha hq

private theorem headP {h args : A → Nat} (hh : Primrec h) (ha : Primrec args) :
    Primrec (fun x => headCode (h x) (args x)) := node2P 4 hh ha

private theorem appP {a b f u : A → Nat} (ha : Primrec a) (hb : Primrec b)
    (hf : Primrec f) (hu : Primrec u) : Primrec (fun x => appCode (a x) (b x) (f x) (u x)) :=
  headP (pairP (Primrec.const 4) (pairP ha hb)) (consP hf (consP hu (Primrec.const 0)))

private theorem stepTypeP {a : A → Nat} (ha : Primrec a) :
    Primrec (fun x => stepTypeCode (a x)) := arrowP (Primrec.const 0) (arrowP ha ha)

private theorem recP {a u step base : A → Nat} (ha : Primrec a) (hu : Primrec u)
    (hs : Primrec step) (hb : Primrec base) :
    Primrec (fun x => recCode (a x) (u x) (step x) (base x)) :=
  appP ha ha
    (appP (stepTypeP ha) (arrowP ha ha)
      (appP (Primrec.const 0) (arrowP (stepTypeP ha) (arrowP ha ha))
        (headP (pairP (Primrec.const 3) ha) (Primrec.const 0)) hu) hs) hb

private theorem leftP {a p : A → Nat} (ha : Primrec a) (hp : Primrec p) :
    Primrec (fun x => leftCode (a x) (p x)) :=
  appP ha (arrowP ha ha) (lamP ha (lamP ha (boundP ha (Primrec.const 1)))) hp

end Programs

private theorem tierTypePrimitive : Primrec tierTypeCode := by
  have hs : Primrec₂ (fun (_ : Nat) (a : Nat) => arrowCode a a) :=
    (arrowP Primrec.snd Primrec.snd).to₂
  exact Primrec.nat_rec₁ indexCode hs

private theorem wrapPrimitive : Primrec (fun x : Nat × Nat × Nat => wrapCode x.1 x.2.1 x.2.2) := by
  have hs : Primrec (fun x : (Nat × Nat × Nat) × (Nat × Nat) =>
      lamCode (tierTypeCode (x.2.1 + x.1.1)) x.2.2) :=
    lamP (tierTypePrimitive.comp (Primrec.nat_add.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))) (Primrec.snd.comp Primrec.snd)
  exact Primrec.nat_rec' (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd) hs.to₂

private theorem bindersPrimitive : Primrec₂ bindersCode :=
  wrapPrimitive.comp ((Primrec.const 1).pair (Primrec.fst.pair Primrec.snd))

private theorem eraseTierPrimitive : Primrec₂ eraseTierCode :=
  wrapPrimitive.comp ((Primrec.const 0).pair (Primrec.fst.pair
    (boundP (Primrec.const indexCode) (Primrec.nat_add.comp Primrec.snd Primrec.fst))))

private theorem iteratorPrimitive : Primrec iteratorCode := by
  have b := tierTypePrimitive
  have eta := arrowP b b
  have erase : Primrec (fun l => eraseTierCode (l+1) 3) :=
    eraseTierPrimitive.comp Primrec.succ (Primrec.const 3)
  exact lamP (Primrec.const indexCode) (lamP eta (lamP b
    (recP b (Primrec.const zeroCode)
      (lamP (Primrec.const 0) (appP eta eta (leftP eta (boundP eta (Primrec.const 2))) erase))
      (boundP b (Primrec.const 0)))))

private theorem appliedP {A : Type} [Primcodable A] {l i p u : A → Nat}
    (hl : Primrec l) (hi : Primrec i) (hp : Primrec p) (hu : Primrec u) :
    Primrec (fun x => appliedCode (l x) (i x) (p x) (u x)) := by
  have b := tierTypePrimitive.comp hl
  have eta := arrowP b b
  exact appP b b (appP eta eta
    (appP (Primrec.const indexCode) (arrowP eta eta) (iteratorPrimitive.comp hl) hi) hp) hu

private theorem slotPrimitive : Primrec slotCode := boundP tierTypePrimitive Primrec.id

private theorem natDownStepPrimitive : Primrec natDownStep :=
  (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1)).pair
    (appP (tierTypePrimitive.comp Primrec.fst) (tierTypePrimitive.comp Primrec.fst)
      Primrec.snd (slotPrimitive.comp Primrec.fst))

private theorem natDownPrimitive : Primrec₂ natDownCode := by
  have run : Primrec (fun x : Nat × Nat => (natDownStep^[x.1]) x) :=
    Primrec.nat_iterate Primrec.fst Primrec.id (natDownStepPrimitive.comp Primrec.snd).to₂
  exact appP (Primrec.const indexCode) (Primrec.const indexCode)
    (Primrec.snd.comp run) (Primrec.const towerZeroCode)

private theorem spinePrimitive : Primrec spineCode := by
  have hs : Primrec (fun m => natDownCode m
      (appliedCode (m+1) (boundCode indexCode 0) (slotCode (m+2)) (slotCode (m+1)))) :=
    natDownPrimitive.comp Primrec.id
      (appliedP Primrec.succ (Primrec.const (boundCode indexCode 0))
        (slotPrimitive.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 2)))
        (slotPrimitive.comp Primrec.succ))
  exact (Primrec.nat_casesOn₁
    (appliedCode 0 (boundCode indexCode 0) (slotCode 1) towerZeroCode) hs).of_eq
      (fun n => by cases n <;> rfl)

private theorem towerPrimitive : Primrec towerCode :=
  bindersPrimitive.comp Primrec.succ
    (appP (Primrec.const (tierTypeCode 1)) (Primrec.const (tierTypeCode 1))
      (Primrec.const (fixedCode NativeOrdinalExponentialTargets.ordinalFix))
      (lamP (Primrec.const indexCode) spinePrimitive))

private theorem downStepPrimitive : Primrec downStep :=
  (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1)).pair
    (appP (tierTypePrimitive.comp (Primrec.succ.comp Primrec.fst))
      (tierTypePrimitive.comp (Primrec.succ.comp Primrec.fst)) Primrec.snd
      (towerPrimitive.comp (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1))))

private theorem downPrimitive : Primrec₂ downCode := by
  have run : Primrec (fun x : Nat × Nat => (downStep^[x.1]) x) :=
    Primrec.nat_iterate Primrec.fst Primrec.id (downStepPrimitive.comp Primrec.snd).to₂
  exact Primrec.snd.comp run

theorem sequenceCodePrimitiveRecursive : SequenceCodePrimitiveRecursive := by
  have hs : Primrec (fun l => appCode indexCode indexCode
      (appCode (tierTypeCode 1) (tierTypeCode 1) (downCode l (towerCode l)) veblenCode) baseCode) :=
    appP (Primrec.const indexCode) (Primrec.const indexCode)
      (appP (Primrec.const (tierTypeCode 1)) (Primrec.const (tierTypeCode 1))
        (downPrimitive.comp Primrec.id towerPrimitive) (Primrec.const veblenCode)) (Primrec.const baseCode)
  exact (Primrec.nat_casesOn₁ baseCode
    (Primrec.nat_casesOn₁ (appCode indexCode indexCode veblenCode baseCode) hs)).of_eq
      (fun n => by cases n with | zero => rfl | succ n => cases n <;> rfl)

theorem sequenceCodeComputable : Computable sequenceCode := sequenceCodePrimitiveRecursive.to_comp

/-! Calibration follows the original constructors, without normalization. -/

private def Encoded (q : Expr) (c : Nat) : Prop :=
  ∃ Q, tr q = some Q ∧ encodeTerm Q = c

private theorem encodedBound (a : Ty) (i : Nat) :
    Encoded (.bound a i) (boundCode (encodeTy a) i) := ⟨.bound a i, rfl, rfl⟩

private theorem encodedLam {a : Ty} {q : Expr} {c : Nat} (h : Encoded q c) :
    Encoded (.lam a q) (lamCode (encodeTy a) c) := by
  obtain ⟨Q,hQ,hc⟩ := h
  refine ⟨.lam a Q,by simp only [tr,hQ,Option.map_some],?_⟩
  change lamCode (encodeTy a) (encodeTerm Q) = _
  rw [hc]

private theorem encodedApp {a b : Ty} {f x : Expr} {cf cx : Nat}
    (hf : Encoded f cf) (hx : Encoded x cx) :
    Encoded (app a b f x) (appCode (encodeTy a) (encodeTy b) cf cx) := by
  obtain ⟨F,hF,hf⟩ := hf
  obtain ⟨X,hX,hx⟩ := hx
  refine ⟨.ordinary (.app a b) (.cons F (.cons X .nil)),?_,?_⟩
  · simp only [app,tr,trArgs,hF,hX,Option.bind_some,Option.map_some]
  · change appCode (encodeTy a) (encodeTy b) (encodeTerm F) (encodeTerm X) = _
    rw [hf,hx]

private theorem encodedZero : Encoded zero zeroCode := ⟨.ordinary .zero .nil,rfl,rfl⟩

private theorem encodedRecursor (a : Ty) :
    Encoded (.head (.recursor a) .nil) (headCode (pairCode 3 (encodeTy a)) 0) :=
  ⟨.ordinary (.recursor a) .nil,rfl,rfl⟩

private theorem encodedRec {a : Ty} {u step base : Expr} {cu cs cb : Nat}
    (hu : Encoded u cu) (hs : Encoded step cs) (hb : Encoded base cb) :
    Encoded (recTerm a u step base) (recCode (encodeTy a) cu cs cb) :=
  encodedApp (encodedApp (encodedApp (encodedRecursor a) hu) hs) hb

private theorem encodedLeft (a : Ty) {p : Expr} {c : Nat} (hp : Encoded p c) :
    Encoded (left a p) (leftCode (encodeTy a) c) :=
  encodedApp (encodedLam (encodedLam (encodedBound a 1))) hp

private theorem tierTypeCalibration (l : Nat) : encodeTy (tierType l) = tierTypeCode l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    change arrowCode (encodeTy (tierType l)) (encodeTy (tierType l)) =
      arrowCode (tierTypeCode l) (tierTypeCode l)
    rw [ih]

private theorem encodedErase (l i : Nat) :
    Encoded (eraseBound (nativeShape (tier l)) i) (eraseTierCode l i) := by
  induction l generalizing i with
  | zero => exact encodedBound indexType i
  | succ l ih =>
    change Encoded (.lam (tierType l) (eraseBound (nativeShape (tier l)) (i+1)))
      (lamCode (tierTypeCode l) (wrapCode 0 l (boundCode indexCode (i+(l+1)))))
    have h := encodedLam (a := tierType l) (ih (i+1))
    rw [tierTypeCalibration] at h
    have hi : i+1+l = i+(l+1) := by omega
    simpa only [eraseTierCode,hi] using h

private theorem encodedIterator (l : Nat) :
    Encoded (iterator (nativeShape (tier l))) (iteratorCode l) := by
  unfold iteratorCode
  rw [← tierTypeCalibration l]
  exact encodedLam (encodedLam (encodedLam
    (encodedRec encodedZero
      (encodedLam (encodedApp
        (encodedLeft (.arrow (tierType l) (tierType l))
          (encodedBound (.arrow (tierType l) (tierType l)) 2))
        (encodedErase (l+1) 3))) (encodedBound (tierType l) 0))))

private theorem encodedApplied (l : Nat) {i p u : Expr} {ci cp cu : Nat}
    (hi : Encoded i ci) (hp : Encoded p cp) (hu : Encoded u cu) :
    Encoded (applied (nativeShape (tier l)) i p u) (appliedCode l ci cp cu) := by
  unfold appliedCode
  rw [← tierTypeCalibration l]
  exact encodedApp (encodedApp (encodedApp (encodedIterator l) hi) hp) hu

private theorem encodedTowerZero : Encoded towerZero towerZeroCode :=
  encodedLam (encodedBound .ground 0)

private theorem encodedSlot (j : Nat) : Encoded (boundSlots j) (slotCode j) := by
  simpa only [boundSlots,slotCode,tierTypeCalibration] using encodedBound (tierType j) j

private theorem natDownCode_succ (m v : Nat) :
    natDownCode (m+1) v = natDownCode m
      (appCode (tierTypeCode (m+1)) (tierTypeCode (m+1)) v (slotCode (m+1))) := by
  simp only [natDownCode,Function.iterate_succ_apply,natDownStep,Nat.add_sub_cancel]

private theorem encodedNatDown (m : Nat) {v : Expr} {c : Nat} (hv : Encoded v c) :
    Encoded (natDown m v boundSlots) (natDownCode m c) := by
  induction m generalizing v c with
  | zero => exact encodedApp hv encodedTowerZero
  | succ m ih =>
    rw [natDownCode_succ]
    have h : Encoded (app (tierType (m+1)) (tierType (m+1)) v (boundSlots (m+1)))
        (appCode (tierTypeCode (m+1)) (tierTypeCode (m+1)) c (slotCode (m+1))) := by
      simpa only [tierTypeCalibration] using
        encodedApp (a := tierType (m+1)) (b := tierType (m+1)) hv (encodedSlot (m+1))
    exact ih h

private theorem encodedSpine (l : Nat) :
    Encoded (spine l (.bound indexType 0) boundSlots) (spineCode l) := by
  cases l with
  | zero => exact encodedApplied 0 (encodedBound indexType 0) (encodedSlot 1) encodedTowerZero
  | succ m => exact encodedNatDown m
      (encodedApplied (m+1) (encodedBound indexType 0) (encodedSlot (m+2)) (encodedSlot (m+1)))

private theorem encodedBinders (k : Nat) {q : Expr} {c : Nat} (h : Encoded q c) :
    Encoded (binders k q) (bindersCode k c) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    have hl := encodedLam (a := tierType (k+1)) ih
    simpa only [tierTypeCalibration] using hl

private theorem encodedFixed {q : Expr} (h : Ordinary q) : Encoded q (fixedCode q) := by
  obtain ⟨Q,hQ⟩ := (NumberedWindowOrdinaryDomainProof.termDomain q).mpr h
  refine ⟨Q,hQ,?_⟩
  simp only [fixedCode,literalCode,hQ,Option.map_some,Option.getD_some]

private def emptySignature : Signature := ⟨[],by simp⟩

private theorem encodedFix : Encoded NativeOrdinalExponentialTargets.ordinalFix
    (fixedCode NativeOrdinalExponentialTargets.ordinalFix) :=
  encodedFixed (NativeOrdinalExponentialTypingProof.fixClosed emptySignature).1.2.1

private theorem encodedNext : Encoded NativeOrdinalExponentialTargets.ordinalNext
    (fixedCode NativeOrdinalExponentialTargets.ordinalNext) :=
  encodedFixed (NativeOrdinalExponentialTypingProof.nextClosed emptySignature).1.2.1

private theorem encodedOmega : Encoded NativeOrdinalBasisTargets.omegaCarrier
    (fixedCode NativeOrdinalBasisTargets.omegaCarrier) :=
  encodedFixed (NativeOrdinalExponentialTypingProof.omegaClosed emptySignature).1.2.1

private theorem encodedTower (l : Nat) : Encoded (towerB l) (towerCode l) := by
  apply encodedBinders (l+1)
  have h := encodedApp (a := tierType 1) (b := tierType 1)
    encodedFix (encodedLam (a := indexType) (encodedSpine l))
  simpa only [tierTypeCalibration] using h

private theorem encodedVeblen : Encoded veblenTerm veblenCode := by
  have h := encodedApp (a := tierType 1) (b := tierType 1)
    (encodedApp (a := tierType 2) (b := tierType 2) (encodedTower 1) (encodedTower 0)) encodedNext
  simpa only [tierTypeCalibration] using h

private theorem encodedBase : Encoded baseTerm baseCode := encodedApp encodedVeblen encodedOmega

private theorem downCode_succ (k v : Nat) :
    downCode (k+1) v = downCode k
      (appCode (tierTypeCode (k+2)) (tierTypeCode (k+2)) v (towerCode k)) := by
  simp only [downCode,Function.iterate_succ_apply,downStep,Nat.add_sub_cancel]

private theorem encodedDown (k : Nat) {v : Expr} {c : Nat} (hv : Encoded v c) :
    Encoded (downTerm k v) (downCode k c) := by
  induction k generalizing v c with
  | zero => exact hv
  | succ k ih =>
    rw [downCode_succ]
    have h : Encoded (app (tierType (k+2)) (tierType (k+2)) v (towerB k))
        (appCode (tierTypeCode (k+2)) (tierTypeCode (k+2)) c (towerCode k)) := by
      simpa only [tierTypeCalibration] using
        encodedApp (a := tierType (k+2)) (b := tierType (k+2)) hv (encodedTower k)
    exact ih h

private theorem encodedSequence (n : Nat) : Encoded (sequenceTerm n) (sequenceCode n) := by
  match n with
  | 0 => exact encodedBase
  | 1 => exact encodedApp encodedVeblen encodedBase
  | l+2 =>
    have h := encodedApp (a := indexType) (b := indexType)
      (encodedApp (a := tierType 1) (b := tierType 1)
        (encodedDown l (encodedTower l)) encodedVeblen) encodedBase
    simpa only [tierTypeCalibration] using h

theorem sequenceCodeCalibration : SequenceCodeCalibration := by
  intro n
  obtain ⟨Q,hQ,hc⟩ := encodedSequence n
  simp only [literalCode,hQ,Option.map_some,hc]

theorem nativeCodeCalibration : NativeCodeCalibration := by
  intro S n t ht
  change (literalCode t.val).getD 0 = sequenceCode n
  rw [ht,sequenceCodeCalibration n]
  rfl

theorem fullTowerCode : FullTowerCode :=
  ⟨sequenceCodePrimitiveRecursive,sequenceCodeCalibration,nativeCodeCalibration⟩

#print axioms sequenceCodePrimitiveRecursive
#print axioms sequenceCodeComputable
#print axioms sequenceCodeCalibration
#print axioms nativeCodeCalibration
#print axioms fullTowerCode

end LogicLineages.PersistentMarking.NativeTowerCode
