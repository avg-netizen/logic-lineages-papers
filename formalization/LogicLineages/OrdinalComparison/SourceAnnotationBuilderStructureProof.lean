module
public import LogicLineages.OrdinalComparison.SourceAnnotationBuilderTargets
public import LogicLineages.OrdinalComparison.ScalarAnnotationDataStructureProof
public import LogicLineages.OrdinalComparison.HeadFiniteSurplusStructureProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAnnotationBuilder.Proof
open ScalarAnnotationData AdditiveHeadTree

private theorem repeatTail_erase {k Γ F} (d : Tree k Γ F) (n : Nat) :
    erase (repeatTail d n) = AdmissibleSum.expand (OrdinalSyntax.leftShape n) (fun _ => erase d) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (.add (erase (repeatTail d n)) (erase d) : OrdinalExpression Γ) =
      .add (AdmissibleSum.expand (OrdinalSyntax.leftShape n) (fun _ => erase d)) (erase d)
    rw [ih]

private theorem repeatTail_valid {k Γ F} (d : Tree k Γ F) (n : Nat)
    (hd : Valid d) : Valid (repeatTail d n) := by
  induction n with
  | zero => exact hd
  | succ n ih => exact ⟨ih,hd⟩

theorem repeat_erase {k Γ F} (n : Nat) (d : Tree k Γ F) :
    erase (repeatTree n d) = AdmissibleAssignment.repeated OrdinalSyntax.defaultPolicy .scalarRepeat n (erase d) := by
  cases n with
  | zero => rfl
  | succ n => exact repeatTail_erase d n

theorem repeat_valid {k Γ F} (n : Nat) (d : Tree k Γ F) (hn : 0<n) (hd : Valid d) :
    Valid (repeatTree n d) := by
  cases n with
  | zero => omega
  | succ n => exact repeatTail_valid d n hd

theorem exactRepeat : Targets.ExactRepeat := by
  intro k Γ F n d
  exact ⟨repeat_erase n d,repeat_valid n d⟩

theorem exactSelectedOperators : Targets.ExactSelectedOperators := by
  intro k Γ d hd
  induction d with
  | free q =>
    have hf := HeadFiniteSurplus.Proof.headFree_of_inactive q hd.2
    rw [selectedOperators.eq_def,selectedHeads.eq_def]
    simp [erase,hf]
  | tracked =>
    rw [selectedOperators.eq_def,selectedHeads.eq_def]
    simp [erase,ordinalHeadFree,ordinalHeadOccurs,ordinalHeadComponentOccurs]
  | add a b iha ihb =>
    have ha := iha hd.1
    have hb := ihb hd.2
    by_cases hf : ordinalHeadFree (.add (erase a) (erase b)) = true
    · rw [selectedOperators.eq_def,selectedHeads.eq_def]
      simp [erase,hf]
    · rw [selectedOperators.eq_def,selectedHeads.eq_def]
      simp only [erase,if_neg hf]
      constructor
      · rw [List.map_append,ha.1,hb.1]
      · intro op hop
        rcases List.mem_append.mp hop with hop | hop
        · exact ha.2 op hop
        · exact hb.2 op hop
  | collapse op tail ih =>
    have ht := ih hd.2.2.2
    by_cases hf : ordinalHeadFree (.collapse op.head (erase tail)) = true
    · rw [selectedOperators.eq_def,selectedHeads.eq_def]
      simp [erase,hf]
    · rw [selectedOperators.eq_def,selectedHeads.eq_def]
      simp only [erase,if_neg hf]
      constructor
      · rw [List.map_cons,ht.1]
      · intro op' hop
        rcases List.mem_cons.mp hop with rfl | hop
        · exact ⟨hd.1,hd.2.1⟩
        · exact ht.2 op' hop

end LogicLineages.OrdinalComparison.Source.SourceAnnotationBuilder.Proof
