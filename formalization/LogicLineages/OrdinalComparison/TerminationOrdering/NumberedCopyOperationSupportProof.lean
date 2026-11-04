module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyOperationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelfApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadWindowPrimrecProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyOperationSupportProof
open Source Source.SourceMarkedSyntax NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
  NumberedFiniteUniverse NumberedCopyCertificate NumberedSelfApplication NumberedCopyOperation
open NumberedHeadCodecPrimrec NumberedHeadCodecPrimrecSupportProof
  NumberedDirectCodePrimrecProof NumberedSelfApplicationPrimrecProof

attribute [local irreducible] Primrec

abbrev HeadKind (n : Nat) := Bool ⊕ Fin n

def headKind {n : Nat} : HeadCode (Fin n) → HeadKind n
  | .zero | .succ | .cases _ | .recursor _ => .inl false
  | .application _ _ => .inl true
  | .ranked s => .inr s

theorem headKindPrimitive (n : Nat) : Primrec (@headKind n) := by
  have h : Primrec (fun data : HeadData n => data.elim
      (fun _ => (Sum.inl false : HeadKind n))
      (Sum.elim (fun _ => Sum.inl false) (Sum.elim (fun _ => Sum.inl false)
        (Sum.elim (fun _ => Sum.inl true) Sum.inr)))) :=
    sumElim (Primrec.const (Sum.inl false))
      (sumElim (Primrec.const (Sum.inl false))
        (sumElim (Primrec.const (Sum.inl false))
          (sumElim (Primrec.const (Sum.inl true)) Primrec.sumInr)))
  exact (h.comp (headTo n)).of_eq (by intro head; cases head <;> rfl)

def finiteAbove (n : Nat) (p : Table n × HeadKind n × HeadKind n) : Bool :=
  match p.2.1, p.2.2 with
  | .inr f, .inr g => p.1 f g
  | .inr _, .inl _ => true
  | .inl false, .inl true => true
  | _, _ => false

theorem finiteAbovePrimitive (n : Nat) : Primrec (finiteAbove n) := by
  let Input := Table n × HeadKind n × HeadKind n
  have hleft : Primrec (fun p : Input × Bool =>
      (Sum.casesOn p.1.2.2 (fun b : Bool => !p.2 && b)
        (fun _ : Fin n => false) : Bool)) :=
    Primrec.sumCasesOn (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.and.comp (Primrec.not.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).to₂
      (Primrec.const false).to₂
  have hright : Primrec (fun p : Input × Fin n =>
      (Sum.casesOn p.1.2.2 (fun _ : Bool => true)
        (fun g : Fin n => p.1.1 p.2 g) : Bool)) :=
    Primrec.sumCasesOn (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.const true).to₂
      (Primrec.fin_app.comp
        (Primrec.fin_app.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.fst)) Primrec.snd).to₂
  have h := Primrec.sumCasesOn (Primrec.fst.comp Primrec.snd) hleft.to₂ hright.to₂
  apply h.of_eq
  rintro ⟨table, f, g⟩
  rcases f with b | s
  · rcases g with c | t
    · cases b <;> cases c <;> rfl
    · cases b <;> rfl
  · cases g <;> rfl

theorem headAbovePrimitive : NumberedCopyOperationTargets.ActualHeadAbovePrimitive := by
  intro n
  have h : Primrec (fun p : Table n × HeadCode (Fin n) × HeadCode (Fin n) =>
      finiteAbove n (p.1, headKind p.2.1, headKind p.2.2)) :=
    (finiteAbovePrimitive n).comp
      (Primrec.fst.pair
        (((headKindPrimitive n).comp (Primrec.fst.comp Primrec.snd)).pair
          ((headKindPrimitive n).comp (Primrec.snd.comp Primrec.snd))))
  exact h.of_eq (by
    rintro ⟨table, f, g⟩
    cases f <;> cases g <;>
      simp [finiteAbove, headKind, decodeHead, RecursiveComparison.headAbove, tableAbove])

abbrev CopyInput (n : Nat) :=
  (List (Fin n) × List Ty) × (Table n × HeadCode (Fin n)) × Code (Fin n)
abbrev PayloadInput (n : Nat) := CopyInput n × NumberedCodeAssemblyPrimrecProof.NumberedData n

def copySelfData (n : Nat) (p : PayloadInput n) : SelfData (Fin n) :=
  (p.2.1.pred, p.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2)

theorem copySelfDataPrimitive (n : Nat) : Primrec (copySelfData n) := by
  have h2 : Primrec (fun p : PayloadInput n => p.2.2) := Primrec.snd.comp Primrec.snd
  have h3 := Primrec.snd.comp h2
  have h4 := Primrec.snd.comp h3
  have h5 := Primrec.snd.comp h4
  exact (Primrec.pred.comp (Primrec.fst.comp Primrec.snd)).pair
    ((Primrec.fst.comp h2).pair
      ((Primrec.fst.comp h4).pair ((Primrec.fst.comp h5).pair (Primrec.snd.comp h5))))

def copyOutput (n : Nat) (arity : Fin n → Nat) (p : PayloadInput n) : Code (Fin n) :=
  .ordinary p.1.2.1.2
    (selfCode (copySelfData n p) (headArguments arity (decodeHead p.1.2.1.2)))

theorem copyOutputPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (copyOutput n arity) := by
  have hg : Primrec (fun p : PayloadInput n => p.1.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have hargs := (NumberedHeadSignaturePrimrecProof.headArgumentsPrimitive n arity).comp hg
  have hself := (selfCodePrimitive n).comp ((copySelfDataPrimitive n).pair hargs)
  exact (NumberedCodeAssemblyPrimrecProof.ordinaryPrimitive n).comp (hg.pair hself)

def copyGuard (n : Nat) (arity : Fin n → Nat) (p : PayloadInput n) : Prop :=
  p.2.2.2.1 = headResult (decodeHead p.1.2.1.2) ∧
    RecursiveComparison.headAbove (tableAbove p.1.2.1.1)
      (decodeHead p.2.2.1) (decodeHead p.1.2.1.2) ∧
    HeadInWindow arity p.1.1.1 p.1.1.2 (decodeHead p.1.2.1.2)

instance copyGuardDecidable (n : Nat) (arity : Fin n → Nat) (p : PayloadInput n) :
    Decidable (copyGuard n arity p) := by
  unfold copyGuard
  infer_instance

theorem copyGuardPrimitive (n : Nat) (arity : Fin n → Nat) :
    PrimrecPred (copyGuard n arity) := by
  have hwindow : Primrec (fun p : PayloadInput n => p.1.1) := Primrec.fst.comp Primrec.fst
  have htable : Primrec (fun p : PayloadInput n => p.1.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have hg : Primrec (fun p : PayloadInput n => p.1.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have hf : Primrec (fun p : PayloadInput n => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have htau : Primrec (fun p : PayloadInput n => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have ht := Primrec.eq.comp htau
    ((NumberedHeadSignaturePrimrecProof.headResultPrimitive n).comp hg)
  have ha := ((headAbovePrimitive n).comp (htable.pair (hf.pair hg))).primrecPred
  have hw := ((NumberedHeadWindowPrimrecProof.headWindowPrimitive n arity).comp
    ((Primrec.fst.comp hwindow).pair ((Primrec.snd.comp hwindow).pair hg))).primrecPred
  exact ht.and (ha.and hw)

def copyPayload (n : Nat) (arity : Fin n → Nat) (p : PayloadInput n) :
    Option (Code (Fin n)) :=
  if p.2.1 = 0 then none else
    if copyGuard n arity p then some (copyOutput n arity p) else none

theorem copyPayloadPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (copyPayload n arity) :=
  Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0))
    (Primrec.const none)
    (Primrec.ite (copyGuardPrimitive n arity)
      (Primrec.option_some.comp (copyOutputPrimitive n arity)) (Primrec.const none))

theorem allCopyCodePrimitive : NumberedCopyOperationTargets.ActualAllCopyCodePrimitive := by
  intro n arity
  have hparts : Primrec (fun p : CopyInput n => finiteNumberedParts p.2.2) :=
    (numberedPartsPrimitive n).comp (Primrec.snd.comp Primrec.snd)
  have h := Primrec.option_bind hparts (copyPayloadPrimitive n arity).to₂
  apply h.of_eq
  rintro ⟨⟨symbols, S⟩, ⟨table, g⟩, code⟩
  cases code with
  | numbered k f tau base types extras => cases k <;> rfl
  | var index => rfl
  | lam sigma body => rfl
  | app sigma q a => rfl
  | bottom tau => rfl
  | ordinary f base => rfl
  | argumentsNil => rfl
  | argumentsCons sigma q rest => rfl

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyOperationSupportProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyOperationSupportProof
