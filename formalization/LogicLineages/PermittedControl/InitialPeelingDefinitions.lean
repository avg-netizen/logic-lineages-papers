module
public import LogicLineages.PermittedControl.ThickBlockDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

/-- Original CNF units in descending exponent order, not generated blocks. -/
noncomputable def originalGapUnits (delta : Ordinal.{0}) : List Ordinal :=
  (Ordinal.CNF Ordinal.omega0 delta).flatMap (fun p => List.replicate p.2.card.toNat p.1)

/-- Peel from the low end, retaining exactly the final leading unit. -/
noncomputable def initialPeelingUnits (delta : Ordinal.{0}) : List Ordinal :=
  (originalGapUnits delta).tail.reverse

noncomputable def initialPeelingPass (mu nu delta : Ordinal.{0}) : Prop :=
  let E := Ordinal.log Ordinal.omega0 delta
  let c := relativeProfile mu E
  let d := relativeProfile nu E
  c=d ∨ (∀ a ∈ initialPeelingUnits delta, a < 2) ∨
  ((c=d+1 ∨ d=c+1) ∧
    ((3 ≤ E ∧ ∃ n : Nat, delta=Ordinal.omega0^E+Ordinal.omega0^(2 : Ordinal)+Ordinal.omega0*(n : Ordinal) ∧
      (min c d+actualOrdinalNorm (Ordinal.omega0^E))%2=1) ∨
     (∃ n : Nat, delta=Ordinal.omega0^(2 : Ordinal)*2+Ordinal.omega0*(n : Ordinal) ∧
      (min c d+actualOrdinalNorm (Ordinal.omega0^(2 : Ordinal)))%2=1)))

noncomputable def initialPeelingRadius (mu nu delta : Ordinal.{0}) : Nat :=
  20+actualOrdinalNorm delta+actualOrdinalNorm mu+actualOrdinalNorm nu

end LogicLineages.PermittedControl
