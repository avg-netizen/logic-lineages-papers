module
public import LogicLineages.PermittedControl.ActualFullValueLabelsTargets
import LogicLineages.PermittedControl.ActualCountCoreLabelsLongProof
import LogicLineages.PermittedControl.ActualMixedRowLeadingAnnotationsBuildProof
import LogicLineages.PermittedControl.SelectedCountOnlyClassProof
import LogicLineages.PermittedControl.PreparedParameterActualProof
import LogicLineages.PermittedControl.EntryBasicsProof
import LogicLineages.PermittedControl.EntryLinearProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFullValueLabels
open OrdinalComparison FieldComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand)
open ActualMixedRowLeadingAnnotations
open SelectedCountOnlyClass (prefixTarget prefixNotationExact)

private theorem linearNoLabel (op : LowerOperand) (h : LinearOperand op) :
    operandLabel op = none := by
  cases op with
  | coordinate _ => rfl
  | count _ _ _ => exact False.elim h
  | ordinary r F =>
      cases F with
      | entry a l m => exact False.elim h
      | iterate a =>
          cases a with
          | zero => rfl
          | succ b => exact False.elim h

private theorem ordinaryLabel (r : Nat) (F : ValueField)
    (h : SelectedNonlinearImageBounds.NonlinearField F) :
    operandLabel (.ordinary r F) = some ⟨r,F⟩ := by
  cases F with
  | entry a l m => rfl
  | iterate a =>
      cases a with
      | zero => exact False.elim (Nat.not_lt_zero _ h)
      | succ b => rfl

private theorem ordinaryProper (F : ValueField) (x : Nat) (h : ClosedOrdinaryValueDomain F x) :
    ProperField F := by
  cases F with
  | iterate a => trivial
  | entry a l m => exact h.1

private def HeadAgrees (f ρ : Nat → Nat) : Option Label → Option Nat → Prop
  | none,none => True
  | some l,some v => ActualLabel f ρ l v
  | _,_ => False

private theorem headLabels (f : Nat → Nat) (B : Nat) (select : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (t : WeightedOperand) (v : Nat) (ann : Annotation)
    (actual : LowerOperandActual f ρ t.2 v) (annotated : ActualAnnotation f ρ t v ann)
    (ready : t.1 ≠ 0 → CountTailReady ρ t.2) :
    HeadAgrees f ρ (activeLabel t) (fullValue f ann) := by
  cases ann with
  | zeroWeight =>
      have zero : t.1 = 0 := annotated
      simp [activeLabel,zero,fullValue,HeadAgrees]
  | linear =>
      have nz : t.1 ≠ 0 := annotated.1
      have skipped := linearNoLabel t.2 annotated.2.1
      simp [activeLabel,nz,skipped,fullValue,HeadAgrees]
  | ordinary q =>
      obtain ⟨nz,r,F,same,nonlinear,_,eq⟩ := annotated
      have read : LowerOperandActual f ρ (.ordinary r F) (f q) := by
        simpa only [same,eq] using actual
      have labels : activeLabel t = some ⟨r,F⟩ := by
        simp only [activeLabel,if_neg nz,same,ordinaryLabel r F nonlinear]
      rw [labels]
      exact ⟨ordinaryProper F (ρ r) read.1,read,(preparedTiedProjection.1 f ρ _ _).mpr read⟩
  | count i q κ =>
      obtain ⟨nz,r,lam,mu,same,ann⟩ := annotated
      have funded : CountTailReady ρ (.count r lam mu) := by simpa only [same] using ready nz
      let eta := prefixTarget mu
      let A := countInitial lam.1.repr (ρ r)
      obtain ⟨F,j,k,Q,emitted,_,_,_,first,_,Qeq,_,_,_,proper,read,literal,_⟩ :=
        ActualCountCoreLabels.exactPaidLongCountCoreLabel f B select ρ r lam mu funded.1 funded.2
      have original : FirstEntry f A eta.1.repr i := by
        have annEntry : FirstEntry f A (mu.1.repr + Ordinal.omega0 ^ (2 : Ordinal.{0})) i :=
          ann.2.1
        change FirstEntry f A (prefixTarget mu).1.repr i
        simpa only [prefixNotationExact.2 mu] using annEntry
      have sameEntry := firstEntry_unique f A eta.1.repr i j original first
      have qeq : q = entryNormAt f A i := ann.2.2.1
      have sameValue : q = Q := by rw [qeq,Qeq,sameEntry]
      have active : activeLabel t = some ⟨r,F⟩ := by
        simp only [activeLabel,if_neg nz,same,operandLabel,emitted,Option.map_some]
      rw [active]
      change ActualLabel f ρ ⟨r,F⟩ (f q)
      rw [sameValue]
      exact ⟨proper,read,literal⟩

theorem exactFullValueLabels : ExactFullValueLabels := by
  intro f B select ρ terms values annotations aligned ready
  induction aligned with
  | nil => exact .nil
  | @cons t terms v values ann annotations actual enc annotated tail ih =>
      have head := headLabels f B select ρ t v ann actual annotated (ready t List.mem_cons_self)
      have rest := ih (fun s st => ready s (List.mem_cons_of_mem _ st))
      cases hl : activeLabel t <;> cases hv : fullValue f ann <;>
        simp only [labels,fullValues,List.filterMap_cons,hl,hv] at ⊢ <;>
        rw [hl,hv] at head
      · exact rest
      · exact False.elim head
      · exact False.elim head
      · exact .cons head rest

theorem exactOriginalReadsHaveFullLabels : ExactOriginalReadsHaveFullLabels := by
  intro f B select ρ terms values actual ready
  obtain ⟨annotations,aligned⟩ := buildActualAnnotations f B select ρ terms values actual ready
  exact ⟨annotations,aligned,exactFullValueLabels f B select ρ terms values annotations aligned ready⟩

end LogicLineages.PermittedControl.ActualFullValueLabels
