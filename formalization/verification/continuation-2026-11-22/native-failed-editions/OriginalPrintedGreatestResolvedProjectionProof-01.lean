module
public import LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedProjectionTargets
import LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedProjectionPreparedProof
import LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedProjectionTransportProof
import LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedMatrixProof
import LogicLineages.PermittedControl.OriginalMatrixLinearLowerTableProof
import LogicLineages.PermittedControl.PreparedParameterActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open ActualFiniteOrderBranches (realized)
open OriginalPrintedGreatestGateResolution (resolutionMinimum)
open OriginalPrintedGreatestResolvedMatrix (prefixRows fullRows PacketAccepts exactUniformResolvedMatrix)
open OriginalPrintedPlainMatrixLinearProjection (top replay)
open OriginalPrintedPlainMatrixOrderBranches (SourceAccepts)
open OriginalMatrixLinearLowerTable (Live assignment exactLinearLowerTable)
open PreparedProjection (LowerOperand PreparedInput eliminatePreparedFormula preparedProjectionActual)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)

private theorem combine (f θ : Nat → Nat) (rs ss : List Row) (xs ys : Snapshot)
    (hx : actualRows f θ rs xs) (hy : actualRows f θ ss ys) :
    actualRows f θ (rs ++ ss) (xs ++ ys) := by
  induction rs generalizing xs with
  | nil =>
      cases xs with
      | nil => exact hy
      | cons x xs => exact False.elim hx
  | cons r rs ih =>
      cases xs with
      | nil => exact False.elim hx
      | cons x xs => exact ⟨hx.1,hx.2.1,hx.2.2.1,ih xs hx.2.2.2⟩

private theorem projectActual (ops : List LowerOperand) (q : NormalForm.Formula)
    (ν : Nat → Nat) (prior live : Prop) (stage source : Nat → Prop)
    (fit : PreparedInput ops q)
    (point : live → ∀ z : Nat, q.eval (Function.update ν 0 z) ↔ stage z)
    (forward : ∀ z : Nat, prior → stage z → source z)
    (backward : ∀ z : Nat, source z → prior ∧ live ∧ stage z) :
    ((prior ∧ live ∧ (eliminatePreparedFormula q).eval ν) ↔ ∃ z : Nat, source z) := by
  have kernel := preparedProjectionActual ops q fit ν
  constructor
  · rintro ⟨held,funded,projected⟩
    obtain ⟨z,witness⟩ := kernel.mp projected
    exact ⟨z,forward z held ((point funded z).mp witness)⟩
  · rintro ⟨z,h⟩
    obtain ⟨held,funded,witness⟩ := backward z h
    exact ⟨held,funded,kernel.mpr ⟨z,(point funded z).mpr witness⟩⟩

theorem exactResolvedProjection : ExactResolvedProjection := by
  intro f B hf θ known gates p plain branch member ordered prior positive fixedPrior ops minimum q
  let ρ := realized θ branch
  let rs := ranked known gates p branch
  let ν := assignment f ρ ops
  let available := Live f ρ ops
  let output := replay θ known gates p branch
  let resolvedAt : Nat → Prop := fun z => PacketAccepts f (output z) (prefixRows known gates p branch) p positive
  let stage : Nat → Prop := fun z => minimum ≤ z ∧ resolvedAt z
  let source : Nat → Prop := fun z =>
    minimum ≤ z ∧ prior (output z) ∧ SourceAccepts f (output z) known gates p positive
  have prep := exactResolvedPrepared f θ known gates p plain branch member ordered minimum positive
  have dh := exactLinearLowerTable f ρ (top branch) rs
  have point (live : available) (z : Nat) : q.eval (Function.update ν 0 z) ↔ stage z :=
    prep.2 ν (dh.2.2.1 live) z
  have same (z : Nat) (paid : minimum ≤ z) :
      (prior (output z) ∧ SourceAccepts f (output z) known gates p positive) ↔
        (prior (output z) ∧ resolvedAt z) :=
    exactUniformResolvedMatrix f B hf θ known gates p plain branch member ordered z paid prior positive
  have forward (z : Nat) (pr : prior θ) (h : stage z) : source z :=
    ⟨h.1,(same z h.1).mpr ⟨(fixedPrior z).mpr pr,h.2⟩⟩
  have backward (z : Nat) (h : source z) : prior θ ∧ available ∧ stage z := by
    obtain ⟨paid,pr,actual⟩ := h
    have packet := ((same z paid).mp ⟨pr,actual⟩).2
    obtain ⟨⟨xs,hx,_⟩,ys,hy,_⟩ := packet
    have real : actualRows f (output z) (fullRows known gates p branch) (xs ++ ys) :=
      combine _ _ _ _ _ _ hx hy
    have rankedHit := (transport θ known gates p branch member ordered z
      (fullRows known gates p branch) (fun _ h => h) f (xs ++ ys)).mpr real
    exact ⟨(fixedPrior z).mp pr,dh.2.2.2 z (xs ++ ys) rankedHit,paid,packet⟩
  change ((prior θ ∧ available ∧ (eliminatePreparedFormula q).eval ν) ↔ ∃ z : Nat, source z)
  exact projectActual ops q ν (prior θ) available stage source prep.1 point forward backward

end LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedProjection
