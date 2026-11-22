module
public import LogicLineages.PermittedControl.ActualMixedRowLeadingAnnotationsTargets
import LogicLineages.PermittedControl.ActualCountLeadingErrorStatementChecks
import LogicLineages.PermittedControl.SelectedNonlinearImageBoundsOrbitProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualMixedRowLeadingAnnotations
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open Targets (countCoreConstant)

private theorem annotate (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (t : WeightedOperand) (v : Nat)
    (actual : LowerOperandActual f ρ t.2 v)
    (ready : t.1 ≠ 0 → CountTailReady ρ t.2) :
    ∃ ann, ActualAnnotation f ρ t v ann := by
  by_cases weight : t.1 = 0
  · exact ⟨.zeroWeight,weight⟩
  obtain ⟨a,op⟩ := t
  cases op with
  | coordinate rank => exact ⟨.linear,weight,True.intro,actual⟩
  | ordinary rank F =>
      have nonlinearImage (nonlinear : SelectedNonlinearImageBounds.NonlinearField F) :
          ∃ ann, ActualAnnotation f ρ (a,.ordinary rank F) v ann := by
        obtain ⟨q,bound,value⟩ :=
          SelectedNonlinearImageBounds.ordinaryFullValueImage f B selected
            F (ρ rank) v nonlinear actual.1 actual.2
        exact ⟨.ordinary q,weight,rank,F,rfl,nonlinear,bound,value⟩
      cases F with
      | iterate k =>
          cases k with
          | zero =>
              have value : v = ρ rank := by
                simpa [FieldValue] using actual.2
              exact ⟨.linear,weight,True.intro,value⟩
          | succ k => exact nonlinearImage (Nat.succ_pos k)
      | entry k lam mu => exact nonlinearImage True.intro
  | count rank lam mu =>
      have paid := ready weight
      obtain ⟨below,i,first,orbit,indexed,_,_,equation,_,error⟩ :=
        StatementChecks.fixed_actualCountLeadingError f B selected ρ rank lam mu v
          paid.1 paid.2 actual
      exact ⟨.count i (entryNormAt f (countInitial lam.1.repr (ρ rank)) i)
        (countCoreConstant mu.1.repr),weight,rank,lam,mu,rfl,
        below,first,rfl,orbit,indexed,rfl,equation,error⟩

theorem buildActualAnnotations : BuildActualAnnotations := by
  intro f B selected ρ terms
  induction terms with
  | nil =>
      intro values reads _
      cases values with
      | nil => exact ⟨[],.nil⟩
      | cons v values => exact False.elim reads
  | cons t terms next =>
      intro values reads ready
      cases values with
      | nil => exact False.elim reads
      | cons v values =>
          obtain ⟨actual,encoded,tail⟩ := reads
          have headReady := ready t List.mem_cons_self
          have tailReady (t' : WeightedOperand) (member : t' ∈ terms) :=
            ready t' (List.mem_cons_of_mem _ member)
          obtain ⟨ann,head⟩ := annotate f B selected ρ t v actual headReady
          obtain ⟨annotations,aligned⟩ := next values tail tailReady
          exact ⟨ann :: annotations,.cons actual encoded head aligned⟩

end LogicLineages.PermittedControl.ActualMixedRowLeadingAnnotations
