module
public import LogicLineages.OrdinalComparison.HeterogeneousUnaryAssemblyTargets
public import LogicLineages.OrdinalComparison.WWSourceRenamingProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.HeterogeneousUnaryAssembly.Proof
open SourceTypedPorts ScalarCarrierAccounting
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem shift_injective {Γ} (ps : List Ty) (τ : Ty) :
    Function.Injective (fun x : Variable Γ τ => shiftVariable ps x) := by
  induction ps with
  | nil => exact fun _ _ h => h
  | cons a ps ih =>
    intro x y h
    exact ih (Variable.there.inj h)

private theorem lift_injective {Γ Δ} (r : Renaming Γ Δ)
    (hinj : ∀ τ, Function.Injective (fun x : Variable Γ τ => r x)) (σ τ : Ty) :
    Function.Injective (fun x : Variable (σ :: Γ) τ => r.lift x) := by
  intro x y h
  cases x with
  | here => cases y with
    | here => rfl
    | there y => cases h
  | there x => cases y with
    | here => cases h
    | there y => exact congrArg Variable.there (hinj _ (Variable.there.inj h))

theorem prefixLift_injective {Γ Δ} (r : Renaming Γ Δ)
    (hinj : ∀ τ, Function.Injective (fun x : Variable Γ τ => r x))
    (ps : List Ty) (τ : Ty) :
    Function.Injective (fun x : Variable (ps++Γ) τ => prefixLift r ps x) := by
  induction ps generalizing τ with
  | nil => exact hinj τ
  | cons a ps ih =>
    exact lift_injective (prefixLift r ps) ih a τ

theorem prefixLift_shift {Γ Δ} (r : Renaming Γ Δ) (ps : List Ty) (τ : Ty) (x : Variable Γ τ) :
    prefixLift r ps (shiftVariable ps x) = shiftVariable ps (r x) := by
  induction ps with
  | nil => rfl
  | cons a ps ih => simp only [prefixLift,shiftVariable,Renaming.lift,ih]

private theorem base_injective {Γ} (ops : List (Operator Γ)) :
    ∀ τ, Function.Injective (fun x : Variable Γ τ => baseMap ops x) := by
  induction ops with
  | nil => intro τ x y h; exact h
  | cons op ops ih =>
    intro τ x y h
    exact ih τ (shift_injective op.privateContext τ h)

theorem sharedBaseEmbeddings : Targets.SharedBaseEmbeddings := by
  intro Γ ops
  refine ⟨base_injective ops,?_⟩
  intro op
  exact ⟨prefixLift_injective (baseMap ops) (base_injective ops) op.privateContext,
    shift_injective op.privateContext,prefixLift_shift (baseMap ops) op.privateContext⟩

theorem unitValue_rename {Γ Δ} (r : Renaming Γ Δ) (q : OrdinalExpression Γ) :
    unitValue (ordinalExpressionRename r q) = unitValue q := by
  induction q with
  | var c => rcases c with ⟨τ,x,j⟩; rfl
  | zero | one | omega => rfl
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    simp only [unitValue,ordinalExpressionRename,substitute,denote] at iha ihb ⊢
    rw [iha,ihb]

private theorem assigned_rename {Γ Δ τ} (r : Renaming Γ Δ)
    (t : OriginalTerm Γ τ) (v : OrdinalVector Γ τ.level)
    (hv : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some v) :
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (t.rename r) =
      some (SourceRenaming.renameVector r v) := by
  rw [SourceRenaming.Proof.assignmentNaturality,hv]
  rfl

theorem merged_assignment {Γ} (ops : List (Operator Γ))
    (pair : OriginalTerm (context ops) (Ty.curriedGround 1) × OrdinalVector (context ops) 1)
    (hp : pair ∈ merged ops) :
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy pair.1 = some pair.2 := by
  induction ops with
  | nil => cases hp
  | cons op ops ih =>
    simp only [merged,List.mem_cons,List.mem_map] at hp
    rcases hp with rfl | ⟨p,hp,rfl⟩
    · exact assigned_rename (headMap op ops) op.term op.vector op.assigned
    · exact assigned_rename (shiftVariable op.privateContext) p.1 p.2 (ih p hp)

private theorem pairs_forall₂ {Γ}
    (ps : List (OriginalTerm Γ (Ty.curriedGround 1) × OrdinalVector Γ 1))
    (hp : ∀ p ∈ ps, AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy p.1 = some p.2) :
    List.Forall₂ (fun t v => AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some v)
      (ps.map Prod.fst) (ps.map Prod.snd) := by
  induction ps with
  | nil => exact .nil
  | cons p ps ih =>
    exact .cons (hp p (by simp)) (ih (fun q hq => hp q (by simp [hq])))

theorem exactMergedAssignments : Targets.ExactMergedAssignments := by
  intro Γ ops
  have hlen : (merged ops).length = ops.length := by
    induction ops with
    | nil => rfl
    | cons op ops ih => simp only [merged,List.length_cons,List.length_map,ih]
  refine ⟨hlen,pairs_forall₂ (merged ops) (merged_assignment ops),?_⟩
  clear hlen
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    simp only [vectors,merged,List.map_cons,List.map_map,Function.comp_def,
      SourceRenaming.renameVector,unitValue_rename] at ih ⊢
    apply congrArg (fun vs : List Ordinal => unitValue (op.vector 1) :: vs)
    trans (merged ops).map (fun x => unitValue (x.2 1))
    · apply congrArg (fun f => (merged ops).map f)
      funext x
      exact unitValue_rename (shiftVariable op.privateContext) (x.2 1)
    · exact ih

end LogicLineages.OrdinalComparison.Source.HeterogeneousUnaryAssembly.Proof
