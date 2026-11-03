module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ExecutableDomainBottomTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ExecutableDomainBottomProof
open Source FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains ExecutableDomainBottom

theorem enumerated : ExecutableDomainBottomTargets.Enumerated := by
  intro Symbol inst arity I τ P
  exact (Finset.choose_spec (fun a : Value I τ P => ∀ b,a ≤ b) (enumerateValues I τ P) (leastWitness I τ P)).1

theorem least : ExecutableDomainBottomTargets.Least := by
  intro Symbol inst arity I τ P a
  exact (Finset.choose_spec (fun a : Value I τ P => ∀ b,a ≤ b) (enumerateValues I τ P) (leastWitness I τ P)).2 a

theorem uniqueLeast : ExecutableDomainBottomTargets.UniqueLeast := by
  intro Symbol inst arity I τ P a
  constructor
  · intro ha
    exact le_antisymm (ha _) (least Symbol inst arity I τ P a)
  · rintro rfl
    exact least Symbol inst arity I τ P

theorem weakeningBottom : ExecutableDomainBottomTargets.WeakeningBottom := by
  intro Symbol inst arity I τ P Q h
  have hl : IsLUB (∅ : Set (Value I τ P)) (bottomValue I τ P) :=
    ⟨(by intro a ha; cases ha),fun a _ => least Symbol inst arity I τ P a⟩
  have hw := RecursiveNaturalLatticesProof.weakeningSuprema Symbol inst arity I τ P Q h ∅ _ hl
  rw [Set.image_empty] at hw
  apply le_antisymm
  · exact hw.2 (by intro a ha; cases ha)
  · exact least Symbol inst arity I τ Q _

def zeroLayer {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (P : World I) : Natural I τ (lower I τ) P :=
  ⟨⟨fun _ => ⟨false,(fun _ => false),(fun _ => false)⟩,
    fun Q s _ => bottomValue I s.val.2 Q.val⟩,by
      constructor
      · intro Q s v w hvw; exact le_rfl
      · intro Q R h s v
        exact weakeningBottom Symbol inferInstance arity I s.val.2 Q.val R.val h⟩

theorem zeroLayerLeast {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (P : World I) (a : Natural I τ (lower I τ) P) :
    zeroLayer I τ P ≤ a := by
  constructor
  · intro Q
    exact ⟨bot_le,fun _ => bot_le,fun _ => bot_le⟩
  · intro Q s v
    exact least Symbol inferInstance arity I s.val.2 Q.val _

theorem bottomLayer {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (P : World I) :
    layerView I τ P (bottomValue I τ P)=zeroLayer I τ P := by
  apply le_antisymm
  · have h := (RecursiveNaturalDomainsProof.transportOrder (family I τ)
      (NaturalTupleLayerProof.layerFamily I τ (lower I τ)) (familyEquation I τ) P
      (bottomValue I τ P) (layerFold I τ P (zeroLayer I τ P))).mp
      (least Symbol inferInstance arity I τ P _)
    change layerView I τ P (bottomValue I τ P) ≤ layerView I τ P (layerFold I τ P (zeroLayer I τ P)) at h
    rw [RecursiveNaturalDomainsProof.layerViewFold] at h
    exact h
  · exact zeroLayerLeast I τ P _

theorem allBitsFalse : ExecutableDomainBottomTargets.AllBitsFalse := by
  intro Symbol inst arity I τ P
  rw [bottomLayer]
  rfl

theorem allTablesBottom : ExecutableDomainBottomTargets.AllTablesBottom := by
  intro Symbol inst arity I τ P Q s v
  rw [bottomLayer]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ExecutableDomainBottomProof
