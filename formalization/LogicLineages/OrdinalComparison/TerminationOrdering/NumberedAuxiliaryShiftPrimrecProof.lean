module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryShiftSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeAssemblyPrimrecProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryShiftPrimrecProof
open Source NumberedAuxiliaryCoding NumberedCodeView NumberedAuxiliaryShift NumberedLeastCodeRepresentative
open NumberedHeadCodecPrimrecSupportProof NumberedSyntaxBoundsPrimrecSupportProof
open NumberedOriginalSourceWindowPrimrecProof (parameterSum parameterSumPrimitive)

abbrev Parameters (n : Nat) := Nat × List (Code (Fin n))

def firstChild {n : Nat} (p : Parameters n) : Code (Fin n) := p.2[0]?.getD .argumentsNil
def secondChild {n : Nat} (p : Parameters n) : Code (Fin n) := p.2[1]?.getD .argumentsNil

theorem firstChildPrimitive (n : Nat) : Primrec (@firstChild n) :=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.snd (Primrec.const 0)) (Primrec.const Code.argumentsNil)
theorem secondChildPrimitive (n : Nat) : Primrec (@secondChild n) :=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.snd (Primrec.const 1)) (Primrec.const Code.argumentsNil)

theorem shiftVariablePrimitive : Primrec₂ shiftVariable :=
  (Primrec.ite (Primrec.nat_lt.comp Primrec.snd Primrec.fst) Primrec.snd (Primrec.succ.comp Primrec.snd)).to₂

def viewRebuild (n : Nat) : Parameters n × CodeView n → Code (Fin n) :=
  parameterSum (fun p : Parameters n × Nat => .var (shiftVariable p.1.1 p.2))
    (parameterSum (fun p : Parameters n × (Ty × Code (Fin n)) => .lam p.2.1 (firstChild p.1))
      (parameterSum (fun p : Parameters n × (Ty × Code (Fin n) × Code (Fin n)) =>
        .app p.2.1 (firstChild p.1) (secondChild p.1))
        (parameterSum (fun p : Parameters n × Ty => .bottom p.2)
          (parameterSum (fun p : Parameters n × (HeadCode (Fin n) × Code (Fin n)) => .ordinary p.2.1 (firstChild p.1))
            (parameterSum
              (fun p : Parameters n × NumberedCodeAssemblyPrimrecProof.NumberedData n =>
                .numbered p.2.1 p.2.2.1 p.2.2.2.1 (firstChild p.1) p.2.2.2.2.2.1 (secondChild p.1))
              (parameterSum (fun _ : Parameters n × Unit => .argumentsNil)
                (fun p : Parameters n × (Ty × Code (Fin n) × Code (Fin n)) =>
                  .argumentsCons p.2.1 (firstChild p.1) (secondChild p.1))))))))

theorem numberedContextPrimitive (n : Nat) : Primrec
    (fun p : Parameters n × NumberedCodeAssemblyPrimrecProof.NumberedData n =>
      (p.2.1,p.2.2.1,p.2.2.2.1,firstChild p.1,p.2.2.2.2.2.1,secondChild p.1)) := by
  have hs1 : Primrec (fun p : Parameters n × NumberedCodeAssemblyPrimrecProof.NumberedData n => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hs2 := Primrec.snd.comp hs1
  have hs3 := Primrec.snd.comp hs2
  have hs4 := Primrec.snd.comp hs3
  exact (Primrec.fst.comp Primrec.snd).pair ((Primrec.fst.comp hs1).pair
    ((Primrec.fst.comp hs2).pair (((firstChildPrimitive n).comp Primrec.fst).pair
      ((Primrec.fst.comp hs4).pair ((secondChildPrimitive n).comp Primrec.fst)))))

theorem viewRebuildPrimitive (n : Nat) : Primrec (viewRebuild n) := by
  unfold viewRebuild
  apply parameterSumPrimitive ((NumberedCodeAssemblyPrimrecProof.varPrimitive n).comp
    (shiftVariablePrimitive.comp (Primrec.fst.comp Primrec.fst) Primrec.snd))
  apply parameterSumPrimitive ((NumberedCodeAssemblyPrimrecProof.lamPrimitive n).comp
    ((Primrec.fst.comp Primrec.snd).pair ((firstChildPrimitive n).comp Primrec.fst)))
  apply parameterSumPrimitive ((NumberedCodeAssemblyPrimrecProof.appPrimitive n).comp
    ((Primrec.fst.comp Primrec.snd).pair (((firstChildPrimitive n).comp Primrec.fst).pair
      ((secondChildPrimitive n).comp Primrec.fst))))
  apply parameterSumPrimitive ((NumberedCodeAssemblyPrimrecProof.bottomPrimitive n).comp Primrec.snd)
  apply parameterSumPrimitive ((NumberedCodeAssemblyPrimrecProof.ordinaryPrimitive n).comp
    ((Primrec.fst.comp Primrec.snd).pair ((firstChildPrimitive n).comp Primrec.fst)))
  apply parameterSumPrimitive ((NumberedCodeAssemblyPrimrecProof.numberedPrimitive n).comp (numberedContextPrimitive n))
  exact parameterSumPrimitive (Primrec.const Code.argumentsNil)
    ((NumberedCodeAssemblyPrimrecProof.argumentsConsPrimitive n).comp
      ((Primrec.fst.comp Primrec.snd).pair (((firstChildPrimitive n).comp Primrec.fst).pair
        ((secondChildPrimitive n).comp Primrec.fst))))

def lambdaFlag {Symbol : Type} : Code Symbol → Nat
  | .lam _ _ => 1
  | _ => 0

def viewLambdaFlag (n : Nat) : CodeView n → Nat :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (Sum.elim (fun _ => 0)
    (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) (fun _ => 0)))))))

theorem lambdaFlagPrimitive (n : Nat) : Primrec (@lambdaFlag (Fin n)) := by
  have h : Primrec (viewLambdaFlag n) := sumElim (Primrec.const 0)
    (sumElim (Primrec.const 1) (sumElim (Primrec.const 0) (sumElim (Primrec.const 0)
      (sumElim (Primrec.const 0) (sumElim (Primrec.const 0) (sumElim (Primrec.const 0) (Primrec.const 0)))))))
  exact (h.comp (NumberedCodeViewProof.viewPrimitive n)).of_eq (by intro code; cases code <;> rfl)

def shiftRequests {n : Nat} (p : Nat × Code (Fin n)) : List (Nat × Code (Fin n)) :=
  (children p.2).map (fun child => (p.1+lambdaFlag p.2,child))

def shiftRecombine {n : Nat} (p : Nat × Code (Fin n)) (values : List (Code (Fin n))) : Option (Code (Fin n)) :=
  some (viewRebuild n ((p.1,values),view p.2))

theorem shiftRequestsPrimitive (n : Nat) : Primrec (@shiftRequests n) :=
  Primrec.list_map ((childrenPrimitive n).comp Primrec.snd)
    (((Primrec.nat_add.comp Primrec.fst ((lambdaFlagPrimitive n).comp Primrec.snd)).comp Primrec.fst).pair Primrec.snd).to₂

theorem shiftRecombinePrimitive (n : Nat) : Primrec₂ (@shiftRecombine n) :=
  (Primrec.option_some.comp ((viewRebuildPrimitive n).comp
    (((Primrec.fst.comp Primrec.fst).pair Primrec.snd).pair
      ((NumberedCodeViewProof.viewPrimitive n).comp (Primrec.snd.comp Primrec.fst))))).to₂

theorem shiftRequestsDecrease (n : Nat) (p child : Nat × Code (Fin n)) (h : child ∈ shiftRequests p) :
    codeNumber child.2<codeNumber p.2 := by
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp h
  exact childrenDecrease n p.2 c hc

theorem shiftRecombineCalibration (n : Nat) (p : Nat × Code (Fin n)) :
    shiftRecombine p ((shiftRequests p).map (fun child => shiftCode child.1 child.2))=some (shiftCode p.1 p.2) := by
  rcases p with ⟨cutoff,code⟩
  cases code <;> simp [shiftRecombine,shiftRequests,viewRebuild,parameterSum,view,lambdaFlag,
    children,firstChild,secondChild,shiftCode]

theorem codeShiftPrimitive : NumberedAuxiliaryShiftTargets.ActualCodeShiftPrimitive := by
  intro n
  exact Primrec.nat_omega_rec' (fun p : Nat × Code (Fin n) => shiftCode p.1 p.2)
    (m := fun p => codeNumber p.2) (l := @shiftRequests n) (g := @shiftRecombine n)
    ((NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n).comp Primrec.snd)
    (shiftRequestsPrimitive n) (shiftRecombinePrimitive n) (shiftRequestsDecrease n) (shiftRecombineCalibration n)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryShiftPrimrecProof
