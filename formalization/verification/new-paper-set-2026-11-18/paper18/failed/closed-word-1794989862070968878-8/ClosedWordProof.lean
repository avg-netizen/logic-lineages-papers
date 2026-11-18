module
public import LogicLineages.StandardControlCurrent.ClosedWordTargets
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineCorrectnessProof
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineLeastProgramsProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.ClosedWordProof
open OrdinalComparison WordLinearDecisionCompletion PolynomialGraphCompletion ClosedWord

 theorem calibration : ClosedWordTargets.BoundCalibration := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro bs p
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      change 6 * Nat.pair (6 * Encodable.encode (boundAtom b).data + 2)
        (withBoundsCode bs (Formula.encode p)) + 4 =
        6 * Nat.pair (6 * Encodable.encode (boundAtom b).data + 2)
        (Formula.encode (withBounds bs p)) + 4
      rw [ih]
  · intro bs p ν
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      simpa [withBounds, Formula.meaningful, Formula.tokens, LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms,
        boundAtom, Atom.row, WordDomain] using ih
  · intro bs p ν
    induction bs with
    | nil => simp [withBounds, BoundsHold]
    | cons b bs ih =>
      simp only [withBounds, List.foldr_cons, Formula.eval]
      have hb : Atom.eval ν (boundAtom b) ↔ b.2 ≤ ν b.1 := by
        simp [Atom.eval, boundAtom, RowValue, wordValue]
      rw [hb]
      change (b.2 ≤ ν b.1 ∧ Formula.eval ν (withBounds bs p)) ↔ _
      rw [ih]
      simp only [BoundsHold, List.mem_cons, forall_eq_or_imp]
      tauto
  · intro D bs p
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      simpa [withBounds, Formula.allowed, Formula.tokens, LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms,
        boundAtom, Atom.row, WordAllowed] using ih

theorem boundCode_primrec : Primrec (fun x : Bounds × Nat => withBoundsCode x.1 x.2) := by
  let A := Bounds × Nat
  have hbound : Primrec (fun b : Nat × Nat => Encodable.encode (boundAtom b).data) := by
    have hrow : Primrec (fun b : Nat × Nat =>
        ((-(b.2 : Int), [((1 : Int), (b.1, ([] : Word)))]) : Row)) :=
      (LayeredComparison.IntegerAlgorithms.Proof.negate_primitive.comp (LayeredComparison.IntegerAlgorithms.Proof.ofNat_primitive.comp Primrec.snd)).pair
        (Primrec.list_cons.comp
          ((Primrec.const (1 : Int)).pair (Primrec.fst.pair (Primrec.const ([] : Word))))
          (Primrec.const []))
    exact Primrec.encode.comp ((Primrec.const 0).pair ((Primrec.const 0).pair hrow))
  have hs : Primrec₂ (fun (_ : A) => fun bq : (Nat × Nat) × Nat =>
      6 * Nat.pair (6 * Encodable.encode (boundAtom bq.1).data + 2) bq.2 + 4) :=
    ((Primrec.const 6).mul (Primrec.natPair.comp
      (((Primrec.const 6).mul (hbound.comp (Primrec.fst.comp Primrec.snd))).add
        (Primrec.const 2)) (Primrec.snd.comp Primrec.snd))).add (Primrec.const 4) |>.to₂
  exact Primrec.list_foldr Primrec.fst Primrec.snd hs

attribute [local irreducible] ClosedWordDecisionCompletion.Machine.solve

theorem programs : ClosedWordTargets.Programs := by
  refine ⟨boundCode_primrec, ?_⟩
  exact ClosedWordDecisionCompletion.MachinePrograms.solve_computable.comp
    (Computable.fst.pair (boundCode_primrec.to_comp.comp Computable.snd))

theorem generalized : ClosedWordTargets.GeneralizedDecision := by
  intro D bs p hp
  have h := ClosedWordDecisionCompletion.MachineProof.actualClosedDecision D
    (withBounds bs p) ((calibration.2.2.2 D bs p).mpr hp)
  unfold solve
  rw [calibration.1]
  rw [h]
  simp only [calibration.2.1, calibration.2.2.1]
  constructor
  · rintro ⟨ν, hd, hb, he⟩
    exact ⟨ν,hb,hd,he⟩
  · rintro ⟨ν,hb,hd,he⟩
    exact ⟨ν,hd,hb,he⟩

theorem source : ClosedWordTargets.SourceDecision := by
  intro D bs p _ hp ha
  rw [generalized D bs p hp]
  constructor
  · rintro ⟨ν,hb,_,he⟩
    exact ⟨ν,hb,he⟩
  · rintro ⟨ν,hb,he⟩
    exact ⟨ν,hb,ha ν hb,he⟩

theorem full : ClosedWordTargets.FullClosedExistential :=
  ⟨calibration,programs,generalized,source⟩
end LogicLineages.StandardControlCurrent.ClosedWordProof
