module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedListCodecPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepCodecPrimrec
open NumberedTypedFocus NumberedStepCertificate NumberedNumericStep

def positionEquiv : Position ≃ Bool ⊕ (Fin 3 × Nat) where
  toFun
    | .lam => .inl false
    | .appFunction => .inl true
    | .ordinaryBase i => .inr (0,i)
    | .numberedBase i => .inr (1,i)
    | .numberedExtras i => .inr (2,i)
  invFun
    | .inl false => .lam
    | .inl true => .appFunction
    | .inr (tag,i) => Fin.cases (.ordinaryBase i)
        (Fin.cases (.numberedBase i) (fun _ => .numberedExtras i)) tag
  left_inv q := by cases q <;> rfl
  right_inv q := by
    rcases q with b | ⟨tag,i⟩
    · cases b <;> rfl
    · rcases tag with ⟨tag,ht⟩
      have h : tag=0 ∨ tag=1 ∨ tag=2 := by omega
      rcases h with rfl | rfl | rfl <;> rfl

instance positionPrimcodable : Primcodable Position := Primcodable.ofEquiv _ positionEquiv

def certificateEquiv : StepCertificate ≃ List Position × Nat × Nat where
  toFun c := (c.path,c.replacement,c.root)
  invFun p := ⟨p.1,p.2.1,p.2.2⟩
  left_inv c := by cases c; rfl
  right_inv p := by rcases p with ⟨a,b,c⟩; rfl

instance certificatePrimcodable : Primcodable StepCertificate := Primcodable.ofEquiv _ certificateEquiv

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepCodecPrimrec
