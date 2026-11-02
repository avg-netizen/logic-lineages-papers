module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryFunctionalNaturalityTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryFunctionalNaturalityProof
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice OrdinaryFunctionalValue FiniteOccurrenceMatching

theorem relatedOfFn {α β : Type} (R : α → β → Prop) (n : Nat) (f : Fin n → α) (g : Fin n → β)
    (h : ∀ i,R (f i) (g i)) : List.Forall₂ R (List.ofFn f) (List.ofFn g) := by
  induction n with
  | zero => simp only [List.ofFn_zero]; exact .nil
  | succ n ih =>
      simp only [List.ofFn_succ]
      exact .cons (h ⟨0,Nat.zero_lt_succ n⟩) (ih (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ))

theorem orderedLift {α β γ : Type} (W : α → γ → Bool) (V : β → γ → Bool)
    {xs : List α} {ys : List β} (h : List.Forall₂ (fun x y => ∀ t,W x t ≤ V y t) xs ys) :
    ∀ ts,List.Forall₂ (fun x t => W x t=true) xs ts → List.Forall₂ (fun y t => V y t=true) ys ts := by
  induction h with
  | nil => intro ts ht; cases ht; exact .nil
  | cons h rest ih =>
      intro ts ht
      cases ht with
      | cons hw ht => exact .cons (Bool.le_iff_imp.mp (h _) hw) (ih _ ht)

theorem weakSourceMono {α β γ : Type} (W : α → γ → Bool) (V : β → γ → Bool)
    {xs : List α} {ys : List β} (h : List.Forall₂ (fun x y => ∀ t,W x t ≤ V y t) xs ys) (ts : List γ) :
    weakTest W xs ts ≤ weakTest V ys ts := by
  apply Bool.le_iff_imp.mpr
  intro hw
  obtain ⟨zs,hz,hm⟩ := (FiniteOccurrenceMatchingProof.weakSpec W xs ts).mp hw
  exact (FiniteOccurrenceMatchingProof.weakSpec V ys ts).mpr ⟨zs,hz,orderedLift W V h zs hm⟩

theorem orderedMapped {α β γ : Type} (W : β → γ → Bool) (V : α → γ → Bool) (f : α → β)
    (xs : List α) (ts : List γ) (h : ∀ x t,t ∈ ts → W (f x) t=V x t) :
    orderedTest W (xs.map f) ts=orderedTest V xs ts := by
  induction xs generalizing ts with
  | nil => cases ts <;> rfl
  | cons x xs ih =>
      cases ts with
      | nil => rfl
      | cons t ts =>
          simp only [List.map_cons,orderedTest]
          rw [h x t (List.mem_cons_self),ih ts (fun x t ht => h x t (List.mem_cons_of_mem _ ht))]

theorem weakMapped {α β γ : Type} (W : β → γ → Bool) (V : α → γ → Bool) (f : α → β)
    (xs : List α) (ts : List γ) (h : ∀ x t,t ∈ ts → W (f x) t=V x t) :
    weakTest W (xs.map f) ts=weakTest V xs ts := by
  apply Bool.eq_iff_iff.mpr
  simp only [weakTest,List.any_eq_true]
  have he : ∀ zs,zs ∈ ts.permutations → orderedTest W (xs.map f) zs=orderedTest V xs zs := by
    intro zs hz
    apply orderedMapped
    intro x t ht
    exact h x t ((List.mem_permutations.mp hz).mem_iff.mp ht)
  exact ⟨fun ⟨zs,hz,hw⟩ => ⟨zs,hz,(he zs hz) ▸ hw⟩,
    fun ⟨zs,hz,hw⟩ => ⟨zs,hz,(he zs hz).symm ▸ hw⟩⟩

theorem basePackingTransport : OrdinaryFunctionalNaturalityTargets.BasePackingTransport := by
  intro Symbol inst arity I f P Q h b
  simp only [packBase,List.map_ofFn]
  rfl

theorem funMonotone : OrdinaryFunctionalNaturalityTargets.FunMonotone := by
  intro Symbol inst arity I f P a b o hab
  have hp : List.Forall₂ (fun p q : Packed I P => ∀ t,pairBit false p t ≤ pairBit false q t) (packBase f a) (packBase f b) := by
    apply relatedOfFn
    intro i t
    exact TypedObservationAccessProof.readMonotone Symbol inst arity I ((headArguments arity f.val).get i) P false (a i) (b i) t (hab i)
  have hm := weakSourceMono (pairBit false) (pairBit false) hp (plainChildren o)
  cases hv : OrdinaryObservationView.rootView o.body with
  | none => simp only [funMatch,hv,le_refl]
  | some data =>
      rcases data with ⟨g,args⟩
      simp only [funMatch,hv]
      apply Bool.le_iff_imp.mpr
      intro ht
      obtain ⟨hhead,hmatch⟩ := Bool.and_eq_true_iff.mp ht
      exact Bool.and_eq_true_iff.mpr ⟨hhead,Bool.le_iff_imp.mp hm hmatch⟩

theorem plainChildPorts {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {B : Nat}
    (o c : Observation Symbol arity Γ B) (hc : c ∈ plainChildren o) : c.ports=o.ports := by
  rw [←OrdinaryObservationViewProof.plainChildrenCalibration Symbol arity Γ B o] at hc
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hc
  rfl

theorem funWeakening : OrdinaryFunctionalNaturalityTargets.FunWeakening := by
  intro Symbol inst arity I f P Q h b o hQo
  have hm : weakTest (pairBit false) (packBase f (weakenBase h b)) (plainChildren o)=weakTest (pairBit false) (packBase f b) (plainChildren o) := by
    rw [←basePackingTransport Symbol inst arity I f P Q h b]
    apply weakMapped
    intro p t ht
    apply TypedObservationAccessProof.restrictionAccess Symbol inst arity I p.1.val P false Q h p.2 t
    rw [plainChildPorts o t ht]
    exact hQo
  cases hv : OrdinaryObservationView.rootView o.body with
  | none => simp only [funMatch,hv]
  | some data => rcases data with ⟨g,args⟩; simp only [funMatch,hv,hm]

theorem bitsMonotone : OrdinaryFunctionalNaturalityTargets.BitsMonotone := by
  intro Symbol inst arity I f M N P a b hr hMN hab Q
  have hbase : weakenBase Q.property a ≤ weakenBase Q.property b := by
    intro i; exact (family I _).restrictMonotone P Q.val Q.property (a i) (b i) (hab i)
  have hm : M.val f ⟨headResult f.val,hr⟩ Q.val ⟨weakenBase Q.property a,emptyExtras I Q.val⟩ ≤
      N.val f ⟨headResult f.val,hr⟩ Q.val ⟨weakenBase Q.property b,emptyExtras I Q.val⟩ :=
    le_trans (hMN f _ Q.val _) (N.property.1 f _ Q.val _ _ ⟨hbase,le_rfl⟩)
  have hread : ∀ o : ObservationAt I (headResult f.val) Q.val,
      TypedObservationAccess.readBit false (M.val f ⟨headResult f.val,hr⟩ Q.val ⟨weakenBase Q.property a,emptyExtras I Q.val⟩) o.val ≤
      TypedObservationAccess.readBit false (N.val f ⟨headResult f.val,hr⟩ Q.val ⟨weakenBase Q.property b,emptyExtras I Q.val⟩) o.val :=
    fun o => TypedObservationAccessProof.readMonotone Symbol inst arity I (headResult f.val) Q.val false _ _ o.val hm
  refine ⟨le_rfl,?_,?_⟩
  · intro o
    apply Bool.le_iff_imp.mpr
    intro ht
    rcases Bool.or_eq_true_iff.mp ht with hf | hm
    · exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.le_iff_imp.mp (funMonotone Symbol inst arity I f Q.val _ _ o.val hbase) hf))
    · exact Bool.or_eq_true_iff.mpr (Or.inr (Bool.le_iff_imp.mp (hread o) hm))
  · exact hread

theorem baseComposition {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {f : HeadIndex I} {P Q R : World I} (h : Extends P Q) (k : Extends Q R) (b : BaseTuple I f P) :
    weakenBase k (weakenBase h b)=weakenBase (fun p hp => k p (h p hp)) b := by
  funext i
  exact (family I _).restrictComposition P Q R h k (b i)

theorem bitsWeakening : OrdinaryFunctionalNaturalityTargets.BitsWeakening := by
  intro Symbol inst arity I f M P Q h b hr
  funext R
  simp only [FiniteObservationBits.weaken,ordinaryBits,baseComposition]

theorem valueMonotone : OrdinaryFunctionalNaturalityTargets.ValueMonotone := by
  intro Symbol inst arity I f M N P a b hMN hab
  let hr := OrdinaryFunctionalValueProof.sourceHeadResultTypes Symbol inst arity I f
  apply (RecursiveNaturalDomainsProof.transportOrder (family I (headResult f.val))
    (NaturalTupleLayerProof.layerFamily I (headResult f.val) (lower I (headResult f.val)))
    (familyEquation I (headResult f.val)) P _ _).mpr
  change (layerView I _ P (ordinaryValue M f a)).val ≤ (layerView I _ P (ordinaryValue N f b)).val
  rw [OrdinaryFunctionalValueProof.ordinaryLayer M f a hr,OrdinaryFunctionalValueProof.ordinaryLayer N f b hr]
  exact FunctionalTupleBuilderProof.builderMonotone Symbol inst arity I M N f ⟨_,hr⟩ P _ _ _ _ hMN
    (bitsMonotone Symbol inst arity I f M N P a b hr hMN hab) ⟨hab,le_rfl⟩

theorem valueWeakening : OrdinaryFunctionalNaturalityTargets.ValueWeakening := by
  intro Symbol inst arity I f M P Q h b
  let hr := OrdinaryFunctionalValueProof.sourceHeadResultTypes Symbol inst arity I f
  apply RecursiveNaturalDomainsProof.layerViewInjective I (headResult f.val) Q
  apply Subtype.ext
  rw [RecursiveNaturalDomainsProof.layerViewWeaken]
  change rawWeaken h (layerView I _ P (ordinaryValue M f b)).val=(layerView I _ Q (ordinaryValue M f (weakenBase h b))).val
  rw [OrdinaryFunctionalValueProof.ordinaryLayer M f b hr,OrdinaryFunctionalValueProof.ordinaryLayer M f (weakenBase h b) hr,
    FunctionalTupleBuilderProof.builderWeakening Symbol inst arity I M f ⟨_,hr⟩ P Q h _ _,
    bitsWeakening Symbol inst arity I f M P Q h b hr]
  have he : (inputFamily I f).restrict h ⟨b,emptyExtras I P⟩=⟨weakenBase h b,emptyExtras I Q⟩ := by
    apply Prod.ext
    · rfl
    · exact OrdinaryFunctionalValueProof.emptyRestriction h
  rw [he]

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryFunctionalNaturalityProof
