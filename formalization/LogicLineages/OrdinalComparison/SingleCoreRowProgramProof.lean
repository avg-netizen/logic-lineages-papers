module
public import LogicLineages.OrdinalComparison.SingleCoreRowSourceProof
public import LogicLineages.OrdinalComparison.OneVariableSignSourceProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SingleCoreRowCompiler

theorem multiple_primitive : Primrec₂ encodedPositiveSourceMultiple := by
  have hs : Primrec₂ (fun source : Nat => fun state : Nat × Nat => 4*Nat.pair state.2 source+2) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4)
      (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.snd) Primrec.fst)) (Primrec.const 2)
  have hrec : Primrec₂ (fun source n : Nat => encodedPositiveSourceMultiple n source) :=
    (Primrec.nat_rec (Primrec.const 0) hs).of_eq (by
      intro source n
      induction n with
      | zero => rfl
      | succ n ih =>
        change 4*Nat.pair (Nat.rec 0 (fun _ previous => 4*Nat.pair previous source+2) n) source+2=_
        rw [ih]
        rfl)
  exact hrec.comp Primrec.snd Primrec.fst

theorem atom_primitive : Primrec encodedSingleCoreAtomPositive := by
  have hhead : Primrec (fun p : SingleCoreAtomCode => p.1) := Primrec.fst
  have ha : Primrec (fun p : SingleCoreAtomCode => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc : Primrec (fun p : SingleCoreAtomCode => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hinput := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4)
    (Primrec₂.natPair.comp (MultivariatePositiveRay.code.1.comp ha)
      (Primrec.nat_mul.comp (Primrec.const 4) hc))) (Primrec.const 2)
  exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4)
    (Primrec₂.natPair.comp hhead hinput)) (Primrec.const 3)

private theorem part_primitive : Primrec₂ encodedSingleCoreRowPart := by
  have hNegative : Primrec (fun p : Bool × EncodedSingleCoreRow => p.1) := Primrec.fst
  have hChoice := Primrec.eq.comp hNegative (Primrec.const true)
  have hConstant : Primrec (fun p : Bool × EncodedSingleCoreRow =>
      if p.1 then p.2.1.2 else p.2.1.1) :=
    Primrec.ite hChoice
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
  have hLinear : Primrec (fun p : Bool × EncodedSingleCoreRow =>
      if p.1 then p.2.2.1.2 else p.2.2.1.1) :=
    Primrec.ite hChoice
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have hN : Primrec (fun p : (Bool × EncodedSingleCoreRow) × (SingleCoreAtomCode × Nat) => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hA : Primrec (fun p : (Bool × EncodedSingleCoreRow) × (SingleCoreAtomCode × Nat) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hRest : Primrec (fun p : (Bool × EncodedSingleCoreRow) × (SingleCoreAtomCode × Nat) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hCoeff := Primrec.fst.comp (Primrec.snd.comp hA)
  have hPart := Primrec.ite (Primrec.eq.comp hN (Primrec.const true)) (Primrec.snd.comp hCoeff) (Primrec.fst.comp hCoeff)
  have hTerm := multiple_primitive.comp hPart (atom_primitive.comp hA)
  have hStep : Primrec₂ (fun p : Bool × EncodedSingleCoreRow => fun state : SingleCoreAtomCode × Nat =>
      4*Nat.pair (encodedPositiveSourceMultiple (if p.1 then state.1.2.1.2 else state.1.2.1.1)
        (encodedSingleCoreAtomPositive state.1)) state.2+2) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4)
      (Primrec₂.natPair.comp hTerm hRest)) (Primrec.const 2)
  have hAtoms : Primrec (fun p : Bool × EncodedSingleCoreRow => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hFold := Primrec.list_foldr hAtoms (Primrec.const 0) hStep
  have hInner := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4)
    (Primrec₂.natPair.comp (MultivariatePositiveRay.code.1.comp hLinear) hFold)) (Primrec.const 2)
  exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4)
    (Primrec₂.natPair.comp (Primrec.nat_mul.comp (Primrec.const 4) hConstant) hInner)) (Primrec.const 2)

theorem parts_primitive : Primrec encodedSingleCoreRowParts :=
  (part_primitive.comp (Primrec.const false) Primrec.id).pair (part_primitive.comp (Primrec.const true) Primrec.id)

theorem parts_program : Targets.ActualSingleCoreRowPartsProgram := by
  refine ⟨multiple_primitive,parts_primitive,?_⟩
  intro row
  exact congrArg₂ Prod.mk (part_code false row) (part_code true row)

theorem sign_program : Computable encodedSingleCoreRowSign := by
  have hP := Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp parts_primitive)
  have hQ := Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp parts_primitive)
  exact ComparisonAssembly.decision_program.comp hP.to_comp hQ.to_comp

end LogicLineages.OrdinalComparison.SingleCoreRowCompiler
