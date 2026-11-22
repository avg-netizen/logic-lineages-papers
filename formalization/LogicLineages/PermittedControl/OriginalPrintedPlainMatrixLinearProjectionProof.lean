module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionTargets
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionPreparedProof
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionTransportProof
import LogicLineages.PermittedControl.OriginalMatrixLinearLowerTableProof
import LogicLineages.PermittedControl.PreparedParameterActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjection
open ActualFiniteOrderBranches (realized)
open OriginalPrintedPlainMatrixInfiniteLow (matrix)
open OriginalPrintedPlainMatrixOrderBranches (renamed)
open OriginalMatrixLinearLowerTable (Live assignment exactLinearLowerTable)
open OriginalPrintedPlainMatrixOrderBranches (SourceAccepts)
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperand PreparedInput eliminatePreparedFormula preparedProjectionActual)

/-- Keep the actual emitted formula abstract while applying the existing
one-variable projection equivalence. -/
private theorem projectWith (ops : List LowerOperand) (q : NormalForm.Formula) (ν : Nat → Nat)
    (fixed live : Prop) (condition source : Nat → Prop) (fit : PreparedInput ops q)
    (point : live → ∀ z : Nat, q.eval (Function.update ν 0 z) ↔ condition z)
    (forward : ∀ z : Nat, fixed → condition z → source z)
    (backward : ∀ z : Nat, source z → fixed ∧ live ∧ condition z) :
    (fixed ∧ live ∧ (eliminatePreparedFormula q).eval ν) ↔ ∃ z : Nat, source z := by
  have kernel := preparedProjectionActual ops q fit ν
  constructor
  · rintro ⟨held,funded,projected⟩
    obtain ⟨z,witness⟩ := kernel.mp projected
    exact ⟨z,forward z held ((point funded z).mp witness)⟩
  · rintro ⟨z,h⟩
    obtain ⟨held,funded,witness⟩ := backward z h
    exact ⟨held,funded,kernel.mpr ⟨z,(point funded z).mpr witness⟩⟩

theorem exactAlreadyLinearCircuitProjection : ExactAlreadyLinearCircuitProjection := by
  intro f θ B known gates p plain branch member checked _ linear prior positive priorFixed
  let ρ := realized θ branch
  let ops := table known gates p branch
  let minimum := safeMinimum B θ known gates p branch
  let q := formula known gates p branch minimum positive
  let ν := assignment f ρ ops
  let available := Live f ρ ops
  let accepts : Nat → Prop := fun z => SourceAccepts f (replay θ known gates p branch z) known gates p positive
  let condition : Nat → Prop := fun z => minimum ≤ z ∧ accepts z
  let sourceAt : Nat → Prop := fun z => minimum ≤ z ∧ prior (replay θ known gates p branch z) ∧ accepts z
  have prep := exactAlreadyLinearPreparedCircuit f θ known gates p plain branch member checked linear minimum positive
  have domains := exactLinearLowerTable f ρ (top branch) (renamed known gates p branch)
  have point (live : available) (z : Nat) : q.eval (Function.update ν 0 z) ↔ condition z :=
    prep.2 ν (domains.2.2.1 live) z
  have forward (z : Nat) (pr : prior θ) (h : condition z) : sourceAt z :=
    ⟨h.1,(priorFixed z).mpr pr,h.2⟩
  have backward (z : Nat) (h : sourceAt z) : prior θ ∧ available ∧ condition z := by
    obtain ⟨ge,pr,source⟩ := h
    obtain ⟨snap,actual⟩ := sourceActual f (replay θ known gates p branch z) known gates p plain positive source
    have full := (transportPart θ known gates p branch member checked z (matrix known gates p)
      (fun _ h => h) f snap).mpr actual
    have live : available := domains.2.2.2 z snap full
    exact ⟨(priorFixed z).mp pr,live,ge,source⟩
  change (prior θ ∧ available ∧ (eliminatePreparedFormula q).eval ν) ↔ ∃ z : Nat, sourceAt z
  exact projectWith ops q ν (prior θ) available condition sourceAt prep.1 point forward backward

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjection
