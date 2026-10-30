module
public import LogicLineages.OrdinalComparison.SourcePortContextsTargets
public import LogicLineages.OrdinalComparison.SourceTypedPortsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePortContextsProof
open SourceTypedPorts SourceTypedPortsProof SourceFreeOccurrences SourcePortContexts SourcePortContextsTargets
open SourceTypeSupport

theorem validPortLength : ValidPortLength := by
  intro B K P hp
  have hc := Finset.card_le_card (Finset.subset_univ (P.map Prod.fst).toFinset)
  simpa only [List.toFinset_card_of_nodup hp.1, List.length_map, Finset.card_univ,
    Fintype.card_fin] using hc

private theorem lists_mem {α : Type} (alphabet : List α) (n : Nat) (xs : List α) :
    xs ∈ listsOfLength alphabet n ↔ xs.length = n ∧ ∀ x ∈ xs, x ∈ alphabet := by
  induction n generalizing xs with
  | zero => cases xs <;> simp [listsOfLength]
  | succ n ih =>
    constructor
    · intro h
      obtain ⟨x, hx, hm⟩ := List.mem_flatMap.mp h
      obtain ⟨ys, hy, rfl⟩ := List.mem_map.mp hm
      obtain ⟨hl, ha⟩ := (ih ys).mp hy
      exact ⟨congrArg Nat.succ hl, by intro y hy; rcases List.mem_cons.mp hy with rfl | hy; exact hx; exact ha y hy⟩
    · rintro ⟨hl, ha⟩
      cases xs with
      | nil => simp at hl
      | cons x xs =>
        exact List.mem_flatMap.mpr ⟨x, ha x (by simp), List.mem_map.mpr ⟨xs,
          (ih xs).mpr ⟨Nat.succ.inj hl, fun y hy => ha y (List.mem_cons_of_mem _ hy)⟩, rfl⟩⟩

theorem portContextEnumeration : PortContextEnumeration := by
  intro B K P
  constructor
  · intro h
    obtain ⟨hm, hn⟩ := List.mem_filter.mp h
    obtain ⟨n, _, hl⟩ := List.mem_flatMap.mp hm
    have ha := ((lists_mem _ n P).mp hl).2
    refine ⟨of_decide_eq_true hn, ?_⟩
    intro p hp
    exact List.mem_toFinset.mpr (List.mem_product.mp (ha p hp)).2
  · intro hp
    apply List.mem_filter.mpr
    refine ⟨?_, decide_eq_true hp.1⟩
    apply List.mem_flatMap.mpr
    refine ⟨P.length, List.mem_range.mpr (Nat.lt_succ_of_le (validPortLength B K.toFinset P hp)), ?_⟩
    apply (lists_mem _ P.length P).mpr
    refine ⟨rfl, ?_⟩
    intro p hmem
    exact List.mem_product.mpr ⟨by simp, List.mem_toFinset.mp (hp.2 p hmem)⟩

private theorem indices_length {Θ Λ : List Ty} (a : PortMap Θ Λ) : (indices a).length = Λ.length := by
  induction a with
  | nil => rfl
  | cons v rest ih => exact congrArg Nat.succ ih

theorem typedAssignmentInjective : TypedAssignmentInjective := by
  intro Γ Θ Λ a hn v w he
  have hi := congrArg (fun z : PackedVariable (Θ ++ Γ) => variableIndex z.2) he
  change variableIndex (renameWith Γ a (embedLeft Γ v.2)) =
    variableIndex (renameWith Γ a (embedLeft Γ w.2)) at hi
  rw [(assignmentRenamingCalibration Γ Θ Λ a).2,
    (assignmentRenamingCalibration Γ Θ Λ a).2] at hi
  have hv : variableIndex v.2 < (indices a).length := by
    rw [indices_length]; exact typedVariableIndex.1 Λ v.1 v.2
  have hw : variableIndex w.2 < (indices a).length := by
    rw [indices_length]; exact typedVariableIndex.1 Λ w.1 w.2
  have hij : variableIndex v.2 = variableIndex w.2 :=
    (List.getD_inj hv hw hn).mp (by simpa only [List.getD_eq_getElem?_getD] using hi)
  exact typedVariableIndex.2 Λ v w hij

private theorem assigned_index_bound {B : Nat} (P : PortContext B) {Λ : List Ty}
    (a : PortMap (portTypes P) Λ) (v : PackedVariable Λ) :
    variableIndex (renameWith [] a (embedLeft [] v.2)) < (P.map Prod.fst).length := by
  have h := typedVariableIndex.1 (portTypes P ++ []) v.1 (renameWith [] a (embedLeft [] v.2))
  simpa only [List.length_append, List.length_nil, Nat.add_zero, portTypes, List.length_map] using h

theorem externalPortAssignment : ExternalPortAssignment := by
  intro B K P Λ a hp ha
  constructor
  · intro v
    refine ⟨(P.map Prod.fst)[variableIndex (renameWith [] a (embedLeft [] v.2))]'(assigned_index_bound P a v), ?_⟩
    exact List.getElem?_eq_getElem (assigned_index_bound P a v)
  · intro v w h
    have hi : variableIndex (renameWith [] a (embedLeft [] v.2)) =
        variableIndex (renameWith [] a (embedLeft [] w.2)) :=
      (List.getElem?_inj (assigned_index_bound P a v) hp.1).mp h
    apply typedAssignmentInjective [] (portTypes P) Λ a ha
    exact typedVariableIndex.2 (portTypes P ++ []) _ _ hi

theorem freshPortExtension : FreshPortExtension := by
  intro B K P i σ hp hi hσ
  refine ⟨⟨?_, ?_⟩, rfl, rfl⟩
  · exact List.nodup_cons.mpr ⟨hi, hp.1⟩
  · intro p hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hσ
    · exact hp.2 p hmem

theorem literalTypeEnumeration : LiteralTypeEnumeration := by
  intro Symbol arity Γ τ t
  induction t with
  | var | zeroC | succC | caseC | recC => simp [literalTypes, typeSupport]
  | app f a ihf iha => simp [literalTypes, typeSupport, List.toFinset_append, ihf, iha]
  | lam body ih => simp [literalTypes, typeSupport, List.toFinset_append, ih]
  | ranked s args ih =>
    have hf : (List.ofFn (fun i : Fin (arity s) => literalTypes (args i))).flatten.toFinset =
        Finset.univ.biUnion (fun i : Fin (arity s) => (literalTypes (args i)).toFinset) := by
      ext σ
      simp
    simp only [literalTypes, typeSupport, List.toFinset_append, hf, ih]

end LogicLineages.OrdinalComparison.Source.SourcePortContextsProof
