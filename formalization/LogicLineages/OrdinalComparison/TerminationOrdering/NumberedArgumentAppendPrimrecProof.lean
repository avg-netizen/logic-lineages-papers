module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectOperationsTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedArgumentAppendPrimrecProof
open Source NumberedAuxiliaryCoding NumberedCodeView NumberedLeastCodeRepresentative NumberedDirectOperations
open NumberedSyntaxBoundsPrimrecSupportProof NumberedHeadCodecPrimrecSupportProof

attribute [local irreducible] Primrec

def argumentParts {Symbol : Type} : Code Symbol → Option (Ty × Code Symbol × Code Symbol)
  | .argumentsCons sigma q rest => some (sigma,q,rest)
  | _ => none

def viewArgumentParts (n : Nat) : CodeView n → Option (Ty × Code (Fin n) × Code (Fin n)) :=
  Sum.elim (fun _ => none) (Sum.elim (fun _ => none) (Sum.elim (fun _ => none)
    (Sum.elim (fun _ => none) (Sum.elim (fun _ => none) (Sum.elim (fun _ => none)
      (Sum.elim (fun _ => none) some))))))

theorem argumentPartsPrimitive (n : Nat) : Primrec (@argumentParts (Fin n)) := by
  have h : Primrec (viewArgumentParts n) := sumElim (Primrec.const none)
    (sumElim (Primrec.const none) (sumElim (Primrec.const none) (sumElim (Primrec.const none)
      (sumElim (Primrec.const none) (sumElim (Primrec.const none) (sumElim (Primrec.const none) Primrec.option_some))))))
  exact (h.comp (NumberedCodeViewProof.viewPrimitive n)).of_eq (by intro code; cases code <;> rfl)

def appendRequests {n : Nat} (p : Code (Fin n) × Code (Fin n)) : List (Code (Fin n) × Code (Fin n)) :=
  match argumentParts p.1 with
  | none => []
  | some d => [(d.2.2,p.2)]

def appendRecombine {n : Nat} (p : Code (Fin n) × Code (Fin n)) (values : List (Code (Fin n))) : Option (Code (Fin n)) :=
  match argumentParts p.1 with
  | none => some p.2
  | some d => some (.argumentsCons d.1 d.2.1 (values[0]?.getD .argumentsNil))

theorem appendRequestsPrimitive (n : Nat) : Primrec (@appendRequests n) := by
  have hb : Primrec (fun p : (Code (Fin n) × Code (Fin n)) × (Ty × Code (Fin n) × Code (Fin n)) =>
      [(p.2.2.2,p.1.2)]) :=
    singletonPrimitive ((Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.fst))
  have h := Primrec.option_casesOn ((argumentPartsPrimitive n).comp Primrec.fst) (Primrec.const []) hb.to₂
  apply h.of_eq
  intro p
  unfold appendRequests
  cases argumentParts p.1 <;> rfl

theorem appendRecombinePrimitive (n : Nat) : Primrec₂ (@appendRecombine n) := by
  have hc : Primrec (fun p : ((Code (Fin n) × Code (Fin n)) × List (Code (Fin n))) ×
      (Ty × Code (Fin n) × Code (Fin n)) => (p.1.2[0]?).getD Code.argumentsNil) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 0))
      (Primrec.const Code.argumentsNil)
  have hb : Primrec (fun p : ((Code (Fin n) × Code (Fin n)) × List (Code (Fin n))) ×
      (Ty × Code (Fin n) × Code (Fin n)) => some (Code.argumentsCons p.2.1 p.2.2.1 (p.1.2[0]?.getD .argumentsNil))) :=
    Primrec.option_some.comp ((NumberedCodeAssemblyPrimrecProof.argumentsConsPrimitive n).comp
      ((Primrec.fst.comp Primrec.snd).pair ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair hc)))
  have h := Primrec.option_casesOn ((argumentPartsPrimitive n).comp (Primrec.fst.comp Primrec.fst))
    (Primrec.option_some.comp (Primrec.snd.comp Primrec.fst)) hb.to₂
  apply h.of_eq
  intro p
  unfold appendRecombine
  cases argumentParts p.1.1 <;> rfl

theorem argumentTailBound (n : Nat) (code : Code (Fin n)) (d : Ty × Code (Fin n) × Code (Fin n))
    (h : argumentParts code=some d) : codeNumber d.2.2<codeNumber code := by
  cases code <;> simp only [argumentParts,Option.some.injEq,reduceCtorEq] at h
  subst d
  exact childrenDecrease n _ _ (by simp [children])

theorem appendRequestsDecrease (n : Nat) (p child : Code (Fin n) × Code (Fin n)) (h : child ∈ appendRequests p) :
    codeNumber child.1<codeNumber p.1 := by
  cases hp : argumentParts p.1 with
  | none => simp [appendRequests,hp] at h
  | some d =>
    have he : child=(d.2.2,p.2) := by simpa [appendRequests,hp] using h
    rw [he]
    exact argumentTailBound n p.1 d hp

theorem appendRecombineCalibration (n : Nat) (p : Code (Fin n) × Code (Fin n)) :
    appendRecombine p ((appendRequests p).map (fun child => appendArgumentCode child.1 child.2))=
      some (appendArgumentCode p.1 p.2) := by
  rcases p with ⟨first,last⟩
  cases first <;> simp [appendRecombine,appendRequests,argumentParts,appendArgumentCode]

theorem argumentAppendPrimitive : NumberedDirectOperationsTargets.ActualArgumentAppendPrimitive := by
  intro n
  have h := Primrec.nat_omega_rec' (fun p : Code (Fin n) × Code (Fin n) => appendArgumentCode p.1 p.2)
    (m := fun p => codeNumber p.1) (l := @appendRequests n) (g := @appendRecombine n)
    ((NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n).comp Primrec.fst)
    (appendRequestsPrimitive n) (appendRecombinePrimitive n) (appendRequestsDecrease n) (appendRecombineCalibration n)
  exact h.to₂

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedArgumentAppendPrimrecProof
