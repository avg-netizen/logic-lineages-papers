module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOpeningPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestExpansionPrimrecSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectCodePrimrecProof
open Source NumberedAuxiliaryCoding NumberedCodeView NumberedDirectOperations
open NumberedHeadCodecPrimrecSupportProof NumberedOpeningPrimrecProof

attribute [local irreducible] Primrec openCode

def ordinaryParts {Symbol : Type} : Code Symbol → Option (HeadCode Symbol × Code Symbol)
  | .ordinary head base => some (head,base)
  | _ => none
def viewOrdinaryParts (n : Nat) : CodeView n → Option (HeadCode (Fin n) × Code (Fin n)) :=
  Sum.elim (fun _ => none) (Sum.elim (fun _ => none) (Sum.elim (fun _ => none)
    (Sum.elim (fun _ => none) (Sum.elim some (fun _ => none)))))

def finiteNumberedParts {n : Nat} : Code (Fin n) → Option (NumberedCodeAssemblyPrimrecProof.NumberedData n)
  | .numbered k head tau base types extras => some (k,head,tau,base,types,extras)
  | _ => none

def viewNumberedParts (n : Nat) : CodeView n → Option (NumberedCodeAssemblyPrimrecProof.NumberedData n) :=
  Sum.elim (fun _ => none) (Sum.elim (fun _ => none) (Sum.elim (fun _ => none)
    (Sum.elim (fun _ => none) (Sum.elim (fun _ => none) (Sum.elim some (fun _ => none))))))

def bottomParts {Symbol : Type} : Code Symbol → Option Ty
  | .bottom tau => some tau
  | _ => none

def viewBottomParts (n : Nat) : CodeView n → Option Ty :=
  Sum.elim (fun _ => none) (Sum.elim (fun _ => none) (Sum.elim (fun _ => none) (Sum.elim some (fun _ => none))))

theorem ordinaryPartsPrimitive (n : Nat) : Primrec (@ordinaryParts (Fin n)) := by
  have h : Primrec (viewOrdinaryParts n) := sumElim (Primrec.const none) (sumElim (Primrec.const none)
    (sumElim (Primrec.const none) (sumElim (Primrec.const none) (sumElim Primrec.option_some (Primrec.const none)))))
  exact (h.comp (NumberedCodeViewProof.viewPrimitive n)).of_eq (by intro code; cases code <;> rfl)

theorem numberedPartsPrimitive (n : Nat) : Primrec (@finiteNumberedParts n) := by
  have h : Primrec (viewNumberedParts n) := sumElim (Primrec.const none) (sumElim (Primrec.const none)
    (sumElim (Primrec.const none) (sumElim (Primrec.const none) (sumElim (Primrec.const none)
      (sumElim Primrec.option_some (Primrec.const none))))))
  exact (h.comp (NumberedCodeViewProof.viewPrimitive n)).of_eq (by intro code; cases code <;> rfl)

theorem bottomPartsPrimitive (n : Nat) : Primrec (@bottomParts (Fin n)) := by
  have h : Primrec (viewBottomParts n) := sumElim (Primrec.const none) (sumElim (Primrec.const none)
    (sumElim (Primrec.const none) (sumElim Primrec.option_some (Primrec.const none))))
  exact (h.comp (NumberedCodeViewProof.viewPrimitive n)).of_eq (by intro code; cases code <;> rfl)

theorem putCodePrimitive (n : Nat) : Primrec (fun p : Nat × Ty × Code (Fin n) => putCode p.1 p.2.1 p.2.2) := by
  have hb : Primrec (fun p : (Nat × Ty × Code (Fin n)) × (HeadCode (Fin n) × Code (Fin n)) =>
      Code.numbered p.1.1 p.2.1 p.1.2.1 p.2.2 [] Code.argumentsNil) :=
    (NumberedCodeAssemblyPrimrecProof.numberedPrimitive n).comp
      ((Primrec.fst.comp Primrec.fst).pair ((Primrec.fst.comp Primrec.snd).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
          ((Primrec.snd.comp Primrec.snd).pair ((Primrec.const []).pair (Primrec.const Code.argumentsNil))))))
  have h := Primrec.option_map ((ordinaryPartsPrimitive n).comp (Primrec.snd.comp Primrec.snd)) hb.to₂
  apply h.of_eq
  rintro ⟨label,tau,code⟩
  cases code <;> rfl

theorem bottomCodePrimitive (n : Nat) : Primrec (fun p : Ty × Code (Fin n) => bottomCode p.1 p.2) := by
  have h := Primrec.option_casesOn ((bottomPartsPrimitive n).comp Primrec.snd)
    (Primrec.option_some.comp ((NumberedCodeAssemblyPrimrecProof.bottomPrimitive n).comp Primrec.fst))
    (Primrec.const none).to₂
  apply h.of_eq
  rintro ⟨tau,code⟩
  cases code <;> rfl

def openingData (n : Nat) (p : NumberedCodeAssemblyPrimrecProof.NumberedData n × (Ty × Ty)) : OpenData (Fin n) :=
  (p.1.1.pred,p.1.2.1,p.2.1,p.2.2,p.1.2.2.2.1,p.1.2.2.2.2.1,p.1.2.2.2.2.2)

theorem openingDataPrimitive (n : Nat) : Primrec (openingData n) := by
  have h2 : Primrec (fun p : NumberedCodeAssemblyPrimrecProof.NumberedData n × (Ty × Ty) => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have h3 := Primrec.snd.comp h2
  have h4 := Primrec.snd.comp h3
  have h5 := Primrec.snd.comp h4
  exact (Primrec.pred.comp (Primrec.fst.comp Primrec.fst)).pair
    ((Primrec.fst.comp h2).pair ((Primrec.fst.comp Primrec.snd).pair
      ((Primrec.snd.comp Primrec.snd).pair ((Primrec.fst.comp h4).pair
        ((Primrec.fst.comp h5).pair (Primrec.snd.comp h5))))))

def abstractionPayload (n : Nat) (d : NumberedCodeAssemblyPrimrecProof.NumberedData n) : Option (Code (Fin n)) :=
  if d.1=0 then none else
    (NumberedRequestExpansionPrimrecSupportProof.arrowParts d.2.2.1).map
      (fun types => Code.lam types.1 (openCode (openingData n (d,types))))

theorem abstractionPayloadPrimitive (n : Nat) : Primrec (abstractionPayload n) := by
  have hl : Primrec (fun p : NumberedCodeAssemblyPrimrecProof.NumberedData n × (Ty × Ty) =>
      Code.lam p.2.1 (openCode (openingData n p))) :=
    (NumberedCodeAssemblyPrimrecProof.lamPrimitive n).comp
      ((Primrec.fst.comp Primrec.snd).pair ((rawOpeningPrimitive n).comp (openingDataPrimitive n)))
  have hm := Primrec.option_map
    (NumberedRequestExpansionPrimrecSupportProof.arrowPartsPrimitive.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))) hl.to₂
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const none) hm

theorem allAbstractionCodePrimitive : NumberedDirectOperationsTargets.ActualAllAbstractionCodePrimitive := by
  intro n
  have h := Primrec.option_bind (numberedPartsPrimitive n) ((abstractionPayloadPrimitive n).comp Primrec.snd).to₂
  apply h.of_eq
  intro code
  cases code with
  | numbered k head tau base types extras => cases k <;> cases tau <;> rfl
  | var index => rfl
  | lam sigma body => rfl
  | app sigma f a => rfl
  | bottom tau => rfl
  | ordinary head base => rfl
  | argumentsNil => rfl
  | argumentsCons sigma q rest => rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectCodePrimrecProof
