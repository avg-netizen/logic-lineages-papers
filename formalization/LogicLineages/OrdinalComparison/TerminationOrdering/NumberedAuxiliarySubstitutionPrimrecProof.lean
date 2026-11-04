module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliarySubstitutionSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliarySubstitutionPrimrecProof
open Source NumberedAuxiliaryCoding NumberedCodeView NumberedLeastCodeRepresentative NumberedAuxiliarySubstitution
open NumberedSyntaxBoundsPrimrecSupportProof NumberedHeadCodecPrimrecSupportProof

def variableIndexOption {Symbol : Type} : Code Symbol → Option Nat
  | .var index => some index
  | _ => none

theorem variableIndexOptionPrimitive (n : Nat) : Primrec (@variableIndexOption (Fin n)) := by
  have h : Primrec (Sum.elim (fun index : Nat => some index)
      (fun _ : (Ty × Code (Fin n)) ⊕ ((Ty × Code (Fin n) × Code (Fin n)) ⊕
        (Ty ⊕ ((HeadCode (Fin n) × Code (Fin n)) ⊕
          ((Nat × HeadCode (Fin n) × Ty × Code (Fin n) × List Ty × Code (Fin n)) ⊕
            (Unit ⊕ (Ty × Code (Fin n) × Code (Fin n))))))) => none)) :=
    sumElim Primrec.option_some (Primrec.const none)
  exact (h.comp (NumberedCodeViewProof.viewPrimitive n)).of_eq (by intro code; cases code <;> rfl)

def lookupCode {Symbol : Type} (environment : List (Code Symbol)) (index : Nat) : Code Symbol :=
  environment[index]?.getD (.var index)

theorem lookupCodePrimitive (n : Nat) : Primrec₂ (@lookupCode (Fin n)) :=
  (Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst Primrec.snd)
    ((NumberedCodeAssemblyPrimrecProof.varPrimitive n).comp Primrec.snd)).to₂

theorem liftEnvironmentPrimitive (n : Nat) : Primrec (@liftEnvironment (Fin n)) := by
  have hs : Primrec (fun p : List (Code (Fin n)) × Code (Fin n) => NumberedAuxiliaryShift.shiftCode 0 p.2) :=
    (NumberedAuxiliaryShiftPrimrecProof.codeShiftPrimitive n).comp ((Primrec.const 0).pair Primrec.snd)
  have hm := Primrec.list_map Primrec.id hs.to₂
  exact Primrec.list_cons.comp (Primrec.const (Code.var 0)) hm

def nextEnvironment {n : Nat} (p : List (Code (Fin n)) × Code (Fin n)) : List (Code (Fin n)) :=
  if NumberedAuxiliaryShiftPrimrecProof.lambdaFlag p.2=1 then liftEnvironment p.1 else p.1

def substitutionRequests {n : Nat} (p : List (Code (Fin n)) × Code (Fin n)) :
    List (List (Code (Fin n)) × Code (Fin n)) :=
  (children p.2).map (fun child => (nextEnvironment p,child))

def substitutionRecombine {n : Nat} (p : List (Code (Fin n)) × Code (Fin n))
    (values : List (Code (Fin n))) : Option (Code (Fin n)) :=
  match variableIndexOption p.2 with
  | some index => some (lookupCode p.1 index)
  | none => some (NumberedAuxiliaryShiftPrimrecProof.viewRebuild n ((0,values),view p.2))

theorem nextEnvironmentPrimitive (n : Nat) : Primrec (@nextEnvironment n) :=
  Primrec.ite (Primrec.eq.comp ((NumberedAuxiliaryShiftPrimrecProof.lambdaFlagPrimitive n).comp Primrec.snd)
    (Primrec.const 1)) ((liftEnvironmentPrimitive n).comp Primrec.fst) Primrec.fst

theorem substitutionRequestsPrimitive (n : Nat) : Primrec (@substitutionRequests n) :=
  Primrec.list_map ((childrenPrimitive n).comp Primrec.snd)
    (((nextEnvironmentPrimitive n).comp Primrec.fst).pair Primrec.snd).to₂

theorem substitutionRecombinePrimitive (n : Nat) : Primrec₂ (@substitutionRecombine n) := by
  have hf : Primrec (fun p : (List (Code (Fin n)) × Code (Fin n)) × List (Code (Fin n)) =>
      some (NumberedAuxiliaryShiftPrimrecProof.viewRebuild n ((0,p.2),view p.1.2))) :=
    Primrec.option_some.comp ((NumberedAuxiliaryShiftPrimrecProof.viewRebuildPrimitive n).comp
      (((Primrec.const 0).pair Primrec.snd).pair
        ((NumberedCodeViewProof.viewPrimitive n).comp (Primrec.snd.comp Primrec.fst))))
  have hv : Primrec (fun p : ((List (Code (Fin n)) × Code (Fin n)) × List (Code (Fin n))) × Nat =>
      some (lookupCode p.1.1.1 p.2)) :=
    Primrec.option_some.comp ((lookupCodePrimitive n).comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
  have h := Primrec.option_casesOn ((variableIndexOptionPrimitive n).comp (Primrec.snd.comp Primrec.fst)) hf hv.to₂
  apply h.of_eq
  intro p
  unfold substitutionRecombine
  cases variableIndexOption p.1.2 <;> rfl

theorem substitutionRequestsDecrease (n : Nat)
    (p child : List (Code (Fin n)) × Code (Fin n)) (h : child ∈ substitutionRequests p) :
    codeNumber child.2<codeNumber p.2 := by
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp h
  exact childrenDecrease n p.2 c hc

theorem substitutionRecombineCalibration (n : Nat) (p : List (Code (Fin n)) × Code (Fin n)) :
    substitutionRecombine p ((substitutionRequests p).map (fun child => substituteCode child.1 child.2))=
      some (substituteCode p.1 p.2) := by
  rcases p with ⟨environment,code⟩
  cases code <;> simp [substitutionRecombine,substitutionRequests,nextEnvironment,variableIndexOption,lookupCode,
    NumberedAuxiliaryShiftPrimrecProof.viewRebuild,NumberedOriginalSourceWindowPrimrecProof.parameterSum,view,
    NumberedAuxiliaryShiftPrimrecProof.lambdaFlag,children,NumberedAuxiliaryShiftPrimrecProof.firstChild,
    NumberedAuxiliaryShiftPrimrecProof.secondChild,substituteCode]

theorem codeSubstitutionPrimitive : NumberedAuxiliarySubstitutionTargets.ActualCodeSubstitutionPrimitive := by
  intro n
  exact Primrec.nat_omega_rec' (fun p : List (Code (Fin n)) × Code (Fin n) => substituteCode p.1 p.2)
    (m := fun p => codeNumber p.2) (l := @substitutionRequests n) (g := @substitutionRecombine n)
    ((NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n).comp Primrec.snd)
    (substitutionRequestsPrimitive n) (substitutionRecombinePrimitive n)
    (substitutionRequestsDecrease n) (substitutionRecombineCalibration n)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliarySubstitutionPrimrecProof
