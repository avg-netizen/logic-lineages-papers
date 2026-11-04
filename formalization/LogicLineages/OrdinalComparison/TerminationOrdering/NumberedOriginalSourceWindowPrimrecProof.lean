module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeSubexpressionsPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceWindowSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceWindowPrimrecProof
open Source NumberedAuxiliaryCoding NumberedCodeView NumberedOriginalSourceWindow
open NumberedHeadCodecPrimrecSupportProof NumberedSyntaxBoundsPrimrecSupportProof
open NumberedTypeSubexpressionsPrimrecProof

def parameterSum {P A B C : Type} (f : P × A → C) (g : P × B → C) (p : P × (A ⊕ B)) : C :=
  p.2.elim (fun a => f (p.1,a)) (fun b => g (p.1,b))

theorem parameterSumPrimitive {P A B C : Type} [Primcodable P] [Primcodable A]
    [Primcodable B] [Primcodable C] {f : P × A → C} {g : P × B → C}
    (hf : Primrec f) (hg : Primrec g) : Primrec (parameterSum f g) :=
  Primrec.sumCasesOn Primrec.snd
    (hf.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂
    (hg.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂

def viewTermRequests (n : Nat) : Ty × CodeView n → List (Request n) :=
  parameterSum (fun _ : Ty × Nat => [])
    (parameterSum (fun p : Ty × (Ty × Code (Fin n)) => [.inl (resultType p.1,p.2.2)])
      (parameterSum (fun p : Ty × (Ty × Code (Fin n) × Code (Fin n)) =>
        [.inl (.arrow p.2.1 p.1,p.2.2.1),.inl (p.2.1,p.2.2.2)])
        (parameterSum (fun _ : Ty × Ty => [])
          (parameterSum (fun p : Ty × (HeadCode (Fin n) × Code (Fin n)) => [.inr p.2.2])
            (parameterSum
              (fun p : Ty × (Nat × HeadCode (Fin n) × Ty × Code (Fin n) × List Ty × Code (Fin n)) =>
                [.inr p.2.2.2.2.1,.inr p.2.2.2.2.2.2])
              (parameterSum (fun _ : Ty × Unit => [])
                (fun _ : Ty × (Ty × Code (Fin n) × Code (Fin n)) => [])))))))

def viewArgumentsRequests (n : Nat) : CodeView n → List (Request n) :=
  Sum.elim (fun _ : Nat => [])
    (Sum.elim (fun _ : Ty × Code (Fin n) => [])
      (Sum.elim (fun _ : Ty × Code (Fin n) × Code (Fin n) => [])
        (Sum.elim (fun _ : Ty => [])
          (Sum.elim (fun _ : HeadCode (Fin n) × Code (Fin n) => [])
            (Sum.elim
              (fun _ : Nat × HeadCode (Fin n) × Ty × Code (Fin n) × List Ty × Code (Fin n) => [])
              (Sum.elim (fun _ : Unit => [])
                (fun p : Ty × Code (Fin n) × Code (Fin n) => [.inl (p.1,p.2.1),.inr p.2.2])))))))

theorem viewTermRequestsPrimitive (n : Nat) : Primrec (viewTermRequests n) := by
  unfold viewTermRequests
  apply parameterSumPrimitive (Primrec.const [])
  apply parameterSumPrimitive
    (singletonPrimitive (Primrec.sumInl.comp ((resultTypePrimitive.comp Primrec.fst).pair (Primrec.snd.comp Primrec.snd))))
  apply parameterSumPrimitive
    (doubletonPrimitive
      (Primrec.sumInl.comp ((NumberedHeadSignaturePrimrecProof.arrowPrimitive.comp
        (Primrec.fst.comp Primrec.snd) Primrec.fst).pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.sumInl.comp ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  apply parameterSumPrimitive (Primrec.const [])
  apply parameterSumPrimitive (singletonPrimitive (Primrec.sumInr.comp (Primrec.snd.comp Primrec.snd)))
  apply parameterSumPrimitive
    (doubletonPrimitive
      (Primrec.sumInr.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
      (Primrec.sumInr.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))))
  exact parameterSumPrimitive (Primrec.const []) (Primrec.const [])

theorem viewArgumentsRequestsPrimitive (n : Nat) : Primrec (viewArgumentsRequests n) := by
  unfold viewArgumentsRequests
  apply sumElim (Primrec.const [])
  apply sumElim (Primrec.const [])
  apply sumElim (Primrec.const [])
  apply sumElim (Primrec.const [])
  apply sumElim (Primrec.const [])
  apply sumElim (Primrec.const [])
  exact sumElim (Primrec.const [])
    (doubletonPrimitive
      (Primrec.sumInl.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
      (Primrec.sumInr.comp (Primrec.snd.comp Primrec.snd)))

theorem requestsPrimitive (n : Nat) : Primrec (@requests n) := by
  have ht : Primrec (fun p : Ty × Code (Fin n) => requests (Sum.inl p)) :=
    ((viewTermRequestsPrimitive n).comp (Primrec.fst.pair ((NumberedCodeViewProof.viewPrimitive n).comp Primrec.snd))).of_eq
      (by intro p; rcases p with ⟨tau,code⟩; cases code <;> rfl)
  have ha : Primrec (fun code : Code (Fin n) => requests (Sum.inr code)) :=
    ((viewArgumentsRequestsPrimitive n).comp (NumberedCodeViewProof.viewPrimitive n)).of_eq
      (by intro code; cases code <;> rfl)
  exact (sumElim ht ha).of_eq (by intro request; cases request <;> rfl)

theorem rootTypesPrimitive (n : Nat) : Primrec (@rootTypes n) :=
  (sumElim (typeSubexpressionsPrimitive.comp Primrec.fst) (Primrec.const [])).of_eq
    (by intro request; cases request <;> rfl)

theorem requestCodePrimitive (n : Nat) : Primrec (@requestCode n) :=
  (sumElim Primrec.snd Primrec.id).of_eq (by intro request; cases request <;> rfl)

theorem recombinePrimitive (n : Nat) : Primrec₂ (@NumberedOriginalSourceWindow.recombine n) :=
  (Primrec.option_some.comp (Primrec.list_append.comp ((rootTypesPrimitive n).comp Primrec.fst)
    (Primrec.list_flatten.comp Primrec.snd))).to₂

theorem allRequestsPrimitive : NumberedOriginalSourceWindowTargets.ActualAllRequestsPrimitive := by
  intro n
  exact Primrec.nat_omega_rec' (@requestValue n)
    (m := fun request => NumberedLeastCodeRepresentative.codeNumber (requestCode request))
    (l := @requests n) (g := @NumberedOriginalSourceWindow.recombine n)
    ((NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n).comp (requestCodePrimitive n))
    (requestsPrimitive n) (recombinePrimitive n)
    (NumberedOriginalSourceWindowSupportProof.requestDecrease n)
    (NumberedOriginalSourceWindowSupportProof.requestRecombineCalibration n)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceWindowPrimrecProof
