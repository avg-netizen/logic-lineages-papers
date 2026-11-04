module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceWindowTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeSubexpressionsPrimrecProof
open Source NumberedLeastCodeRepresentative NumberedTypeCodecPrimrec NumberedTypeCodecPrimrecSupportProof
open NumberedSyntaxBoundsPrimrecSupportProof

def typeChildren : Ty → List Ty
  | .ground => []
  | .arrow sigma tau => [sigma,tau]

def numericChildren : Nat → List Ty
  | 0 => []
  | value+1 => [typeEquiv.symm (Nat.unpair value).1,typeEquiv.symm (Nat.unpair value).2]

theorem numericChildrenPrimitive : Primrec numericChildren := by
  have h : Primrec (fun value : Nat =>
      [typeEquiv.symm (Nat.unpair value).1,typeEquiv.symm (Nat.unpair value).2]) :=
    doubletonPrimitive (typeFrom.comp (Primrec.fst.comp Primrec.unpair))
      (typeFrom.comp (Primrec.snd.comp Primrec.unpair))
  exact (Primrec.nat_casesOn₁ [] h).of_eq (by intro value; cases value <;> rfl)

theorem numericChildrenCalibration (tau : Ty) : numericChildren (typeNumber tau)=typeChildren tau := by
  cases tau with
  | ground => rfl
  | arrow sigma tau =>
    have hs : typeEquiv.symm (typeNumber sigma)=sigma := typeEquiv.symm_apply_apply sigma
    have ht : typeEquiv.symm (typeNumber tau)=tau := typeEquiv.symm_apply_apply tau
    simp only [typeNumber,Nat.add_comm 1,numericChildren,Nat.unpair_pair,hs,ht,typeChildren]

theorem typeChildrenPrimitive : Primrec typeChildren :=
  (numericChildrenPrimitive.comp NumberedTypeCodecPrimrecProof.typeEncoderPrimitive).of_eq numericChildrenCalibration

theorem typeChildrenDecrease (tau child : Ty) (h : child ∈ typeChildren tau) : typeNumber child<typeNumber tau := by
  cases tau with
  | ground => simp [typeChildren] at h
  | arrow sigma tau =>
    have hm : child=sigma ∨ child=tau := by simpa [typeChildren] using h
    rcases hm with hs | ht
    · rw [hs]
      have hp := Nat.left_le_pair (typeNumber sigma) (typeNumber tau)
      change typeNumber sigma<1+Nat.pair (typeNumber sigma) (typeNumber tau)
      omega
    · rw [ht]
      have hp := Nat.right_le_pair (typeNumber sigma) (typeNumber tau)
      change typeNumber tau<1+Nat.pair (typeNumber sigma) (typeNumber tau)
      omega

def typeRecombine (tau : Ty) (values : List (List Ty)) : Option (List Ty) := some (tau::values.flatten)

theorem typeRecombinePrimitive : Primrec₂ typeRecombine :=
  (Primrec.option_some.comp (Primrec.list_cons.comp Primrec.fst (Primrec.list_flatten.comp Primrec.snd))).to₂

theorem typeRecombineCalibration (tau : Ty) :
    typeRecombine tau ((typeChildren tau).map Ty.subtypes)=some tau.subtypes := by
  cases tau <;> simp [typeRecombine,typeChildren,Ty.subtypes]

theorem typeSubexpressionsPrimitive : NumberedOriginalSourceWindowTargets.ActualTypeSubexpressionsPrimitive :=
  Primrec.nat_omega_rec' Ty.subtypes (m := typeNumber) (l := typeChildren) (g := typeRecombine)
    NumberedTypeCodecPrimrecProof.typeEncoderPrimitive typeChildrenPrimitive typeRecombinePrimitive
    typeChildrenDecrease typeRecombineCalibration

def numericResult : Nat → Ty
  | 0 => .ground
  | value+1 => typeEquiv.symm (Nat.unpair value).2

theorem resultTypePrimitive : Primrec NumberedOriginalSourceWindow.resultType := by
  have h : Primrec (fun value : Nat => typeEquiv.symm (Nat.unpair value).2) :=
    typeFrom.comp (Primrec.snd.comp Primrec.unpair)
  have hn : Primrec numericResult :=
    (Primrec.nat_casesOn₁ Ty.ground h).of_eq (by intro value; cases value <;> rfl)
  apply (hn.comp NumberedTypeCodecPrimrecProof.typeEncoderPrimitive).of_eq
  intro tau
  cases tau with
  | ground => rfl
  | arrow sigma tau =>
    have ht : typeEquiv.symm (typeNumber tau)=tau := typeEquiv.symm_apply_apply tau
    simp only [typeNumber,Nat.add_comm 1,numericResult,Nat.unpair_pair,ht,NumberedOriginalSourceWindow.resultType]

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeSubexpressionsPrimrecProof
