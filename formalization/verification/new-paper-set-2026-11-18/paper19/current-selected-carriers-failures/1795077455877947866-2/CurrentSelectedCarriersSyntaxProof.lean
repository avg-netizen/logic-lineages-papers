module
public import LogicLineages.ControlSensitivityCurrent.CurrentSelectedCarriersTargets
public import LogicLineages.OrdinalComparison.WWUnaryCarrierProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentSelectedCarriers

open LogicLineages.OrdinalComparison.Source
open SourceFreeOccurrences AdmissibleAssignment

theorem exactFreshRename : CurrentSelectedCarriersTargets.ExactFreshRename := by
  intro Γ σ F
  induction F with
  | here =>
    refine ⟨rfl,?_⟩
    intro τ x hn
    cases x with
    | here => exact (hn rfl).elim
    | there x => rfl
  | @there Γ σ δ F ih =>
    obtain ⟨hs,ho⟩ := ih
    constructor
    · change insertSecond (renameTrackedAt F F) = _
      rw [hs] <;> rfl
    · intro τ x hn
      cases x with
      | here => rfl
      | there x =>
        have hx : (⟨_,x⟩ : PackedVariable Γ) ≠ ⟨σ,F⟩ := by
          intro he
          exact hn (congrArg (fun y : PackedVariable Γ =>
            (⟨y.1,.there y.2⟩ : PackedVariable (δ :: Γ))) he)
        have he := ho _ x hx
        change insertSecond (renameTrackedAt F x) = _
        rw [he] <;> rfl

private theorem renameNoOld {Γ : List Ty} {σ τ : Ty} (F : Variable Γ σ)
    (t : OriginalTerm Γ τ) :
    (⟨σ,.there F⟩ : PackedVariable (σ :: Γ)) ∉ freeOccurrences (t.rename (renameTrackedAt F)) := by
  rw [SourceFreeOccurrencesProof.freeOccurrenceRenaming Empty Empty.elim Γ (σ :: Γ) τ t (renameTrackedAt F)]
  intro h
  obtain ⟨⟨υ,x⟩,hx,he⟩ := List.mem_map.mp h
  by_cases hF : (⟨υ,x⟩ : PackedVariable Γ) = ⟨σ,F⟩
  · rw [hF] at he
    change (⟨σ,renameTrackedAt F F⟩ : PackedVariable (σ :: Γ)) = ⟨σ,.there F⟩ at he
    rw [(exactFreshRename Γ σ F).1] at he
    have hbad : (none : Option (PackedVariable Γ)) = some ⟨σ,F⟩ :=
      congrArg dropBound he
    cases hbad
  · change (⟨υ,renameTrackedAt F x⟩ : PackedVariable (σ :: Γ)) = ⟨σ,.there F⟩ at he
    rw [(exactFreshRename Γ σ F).2 υ x hF] at he
    have hsame : some (⟨υ,x⟩ : PackedVariable Γ) = some ⟨σ,F⟩ :=
      congrArg dropBound he
    exact hF (Option.some.inj hsame)

private theorem saturationOccurrences {Γ : List Ty} (r : Nat)
    (t : OriginalTerm Γ (Ty.curriedGround (r+1))) :
    freeOccurrences (UnaryCarrier.saturate r t) = freeOccurrences t := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change freeOccurrences (UnaryCarrier.saturate r (.app t .zeroC)) = _
    rw [ih]
    simp [freeOccurrences]

theorem carrierNoGround {Γ : List Ty} {σ : Ty} (F : Variable Γ σ) (r : Nat)
    (t : OriginalTerm Γ (Ty.curriedGround (r+1))) (x : Variable (σ :: Γ) .ground) :
    (⟨Ty.ground,x⟩ : PackedVariable (σ :: Γ)) ∉ freeOccurrences (carrierAt F r t) :=
  UnaryCarrier.Proof.closeGround_no_ground (UnaryCarrier.saturate r (t.rename (renameTrackedAt F))) x

theorem carrierNoOld {Γ : List Ty} {σ : Ty} (F : Variable Γ σ) (r : Nat)
    (t : OriginalTerm Γ (Ty.curriedGround (r+1))) :
    (⟨σ,.there F⟩ : PackedVariable (σ :: Γ)) ∉ freeOccurrences (carrierAt F r t) := by
  let s := UnaryCarrier.saturate r (t.rename (renameTrackedAt F))
  have hn : (⟨σ,.there F⟩ : PackedVariable (σ :: Γ)) ∉ freeOccurrences s := by
    unfold s
    rw [saturationOccurrences]
    exact renameNoOld F t
  change (⟨σ,.there F⟩ : PackedVariable (σ :: Γ)) ∉ freeOccurrences (UnaryCarrier.closeGround s)
  rw [UnaryCarrier.closeGround,SourceFreeOccurrencesProof.exactFreeOccurrenceSubstitution]
  simp only [List.mem_flatMap]
  rintro ⟨⟨υ,x⟩,hx,he⟩
  cases υ with
  | ground =>
    simp [UnaryCarrier.groundMap,GroundClosing.GroundMap.source,GroundClosing.Image.source,
      freeOccurrences] at he
  | arrow a b =>
    have hsame : (⟨σ,.there F⟩ : PackedVariable (σ :: Γ)) = ⟨Ty.arrow a b,x⟩ :=
      List.mem_singleton.mp he
    exact hn (hsame.symm ▸ hx)

private theorem applicationPositive (p : AdmissibleSum.Policy) {Γ : List Ty} {τ : Ty}
    (u : OrdinalVector Γ (max 1 τ.level)) (g : OrdinalVector Γ 0)
    (j : Fin (τ.level+1)) (hj : 0 < j.val) :
    application (σ := .ground) (τ := τ) p u g j =
      u ⟨j.val, by have := j.isLt; omega⟩ := by
  simp only [application,box,Ty.level,show j.val ≠ 0 from Nat.ne_of_gt hj,↓reduceIte]
  rw [ordinalBoxPositive]
  simp only [show ¬ j.val ≤ 0 by omega,↓reduceDIte,ordinalVectorAt]
  simp only [show j.val < max 1 τ.level+1 by have := j.isLt; omega,↓reduceDIte]

private theorem saturateAssignment (p : AdmissibleSum.Policy) {Γ : List Ty} (r : Nat)
    (t : OriginalTerm Γ (Ty.curriedGround (r+1)))
    (u : OrdinalVector Γ (Ty.curriedGround (r+1)).level)
    (hu : assignment p t = some u) :
    ∃ v : OrdinalVector Γ 1,
      assignment p (UnaryCarrier.saturate r t) = some v ∧ v 1 = u (UnaryCarrier.headIndex r) := by
  cases r with
  | zero => exact ⟨u,hu,rfl⟩
  | succ r =>
    let g : OrdinalVector Γ 0 := fun _ => .one
    let a := application (σ := .ground) (τ := Ty.curriedGround (r+1)) p u g
    have ha : assignment p (.app t .zeroC) = some a := by
      change (assignment p t).bind (fun vf => some (application p vf g)) = some a
      rw [hu] <;> rfl
    obtain ⟨v,hv,he⟩ := saturateAssignment p r (.app t .zeroC) a ha
    refine ⟨v,hv,he.trans ?_⟩
    exact applicationPositive p u g (UnaryCarrier.headIndex r) (by change 0 < 1; decide)
termination_by r

theorem groundSaturation : CurrentSelectedCarriersTargets.GroundSaturation := by
  intro p Γ r t u hu
  exact saturateAssignment p r t u hu

end LogicLineages.ControlSensitivityCurrent.CurrentSelectedCarriers
