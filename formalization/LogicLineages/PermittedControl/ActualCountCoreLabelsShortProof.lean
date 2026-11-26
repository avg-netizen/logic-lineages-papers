module
public import LogicLineages.PermittedControl.ActualCountCoreLabelsTargets
import LogicLineages.PermittedControl.ActualCountCoreLabelsSyntaxProof
import LogicLineages.PermittedControl.ShortFieldGapProof
import LogicLineages.PermittedControl.EntryLinearProof
import LogicLineages.PermittedControl.PreparedParameterActualProof
import LogicLineages.OrdinalComparison.OrdinalRepresentationSound

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCountCoreLabels
open OrdinalComparison FieldComparison PreparedProjection

theorem exactShortCountHasNoCoreLabel : ExactShortCountHasNoCoreLabel := by
  intro f B selected ρ rank lam mu proper afford k positive
  have classified := (exactCountCoreClassifier lam mu).2.1 proper positive
  have noLabel : fieldLabel lam mu = none := by simp only [fieldLabel,classified]
  have endpointEq : lam.1.repr = mu.1.repr + Ordinal.omega0 * (k : Ordinal) :=
    (shortGapRecognition lam mu proper k positive).2.2.mp rfl
  have under := proper.2.2.trans (normalRepresentationSound lam)
  have entered := linear_entry f (selected_threshold_admissible f B selected).2
    mu.1.repr proper.2.1 under k (ρ rank-actualOrdinalNorm lam.1.repr)
  have start : countInitial lam.1.repr (ρ rank) = mu.1.repr +
      (Ordinal.omega0 * (k : Ordinal) + ((ρ rank-actualOrdinalNorm lam.1.repr : Nat) : Ordinal)) := by
    change lam.1.repr + ((ρ rank-actualOrdinalNorm lam.1.repr : Nat) : Ordinal) = _
    rw [endpointEq,add_assoc]
  rw [← start] at entered
  have actual : LowerOperandActual f ρ (.count rank lam mu) k := ⟨⟨proper,afford⟩,entered⟩
  exact ⟨classified,noLabel,entered,(preparedTiedProjection.1 f ρ _ k).mpr actual⟩

end LogicLineages.PermittedControl.ActualCountCoreLabels
