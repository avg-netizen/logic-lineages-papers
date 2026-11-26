module
public import LogicLineages.PermittedControl.ClosedOrdinaryFieldTargets
import LogicLineages.PermittedControl.ClosedOrdinaryFieldGuardProof
import LogicLineages.PermittedControl.FixedEntryClosedScanEffectiveProof

@[expose] public section
namespace LogicLineages.PermittedControl.FieldComparison

private theorem finite_iterate_computable (f : Nat → Nat) (hf : Computable f) :
    Computable₂ (fun a (x : Nat) => f^[a] x) := by
  have hstep : Computable₂ (fun (_ : Nat × Nat) (p : Nat × Nat) => f p.2) :=
    hf.comp (Computable.snd.comp Computable.snd)
  exact (Computable.nat_rec Computable.fst Computable.snd hstep).of_eq (fun p => by
    rcases p with ⟨n,x⟩
    induction n with
    | zero => rfl
    | succ n ih =>
      change Nat.rec x (fun _ v => f v) (n+1) = f^[n+1] x
      rw [Function.iterate_succ_apply']
      exact congrArg f ih)

private theorem closed_result_computable (f : Nat → Nat) (hf : Computable f) :
    Computable (closedProperEntryResult f) := by
  have hscan := ((fixedEntryClosedEffective.2 f).2 hf).2
  exact (Computable.cond closedProperEntryDomainExact.1.to_comp hscan (Computable.const none)).of_eq
    (fun p => by cases h : closedProperEntryGuard p <;> simp [closedProperEntryResult,h])

private theorem option_mapped_iterate_computable (f : Nat → Nat) (hf : Computable f) :
    Computable₂ (fun (a : Nat) (r : Option (Nat × Nat)) => r.map (fun v => f^[a] v.1)) := by
  have ha : Computable (fun p : (Nat × Option (Nat × Nat)) × (Nat × Nat) => p.1.1) :=
    Computable.fst.comp Computable.fst
  have hval : Computable (fun p : (Nat × Option (Nat × Nat)) × (Nat × Nat) => p.2.1) :=
    Computable.fst.comp Computable.snd
  exact Computable.option_map Computable.snd ((finite_iterate_computable f hf).comp ha hval)

private theorem option_mapped_count_computable :
    Computable (fun r : Option (Nat × Nat) => r.map Prod.snd) :=
  Computable.option_map Computable.id (Computable.snd.comp Computable.snd)

private abbrev ValueArgs := LongFieldCode × Nat

private theorem closed_value_computable (f : Nat → Nat) (hf : Computable f) :
    Computable₂ (closedOrdinaryValueField f) := by
  have htag : Computable (fun p : ValueArgs => p.1.1) := Computable.fst.comp Computable.fst
  have ha : Computable (fun p : ValueArgs => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hl : Computable (fun p : ValueArgs => p.1.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hm : Computable (fun p : ValueArgs => p.1.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hx : Computable (fun p : ValueArgs => p.2) := Computable.snd
  have hiterate : Computable (fun p : ValueArgs => some (some (f^[p.1.2.1] p.2))) :=
    Computable.option_some.comp (Computable.option_some.comp ((finite_iterate_computable f hf).comp ha hx))
  have hentry := (closed_result_computable f hf).comp (hl.pair (hm.pair hx))
  have hresult : Computable (fun p : ValueArgs =>
      (closedProperEntryResult f (p.1.2.2.1,p.1.2.2.2,p.2)).map
        (fun r => r.map (fun v => f^[p.1.2.1] v.1))) :=
    Computable.option_map hentry
      ((option_mapped_iterate_computable f hf).comp (ha.comp Computable.fst) Computable.snd)
  have hguard : Computable (fun p : ValueArgs => decide (p.1.1 = 0)) :=
    Primrec.eq.decide.to_comp.comp htag (Computable.const 0)
  refine (Computable.cond hguard hiterate hresult).of_eq (fun p => ?_)
  rcases p with ⟨⟨tag,a,lam,mu⟩,x⟩
  by_cases h : tag = 0 <;> simp [closedOrdinaryValueField,h]

private theorem closed_count_computable (f : Nat → Nat) (hf : Computable f) :
    Computable (closedOrdinaryCountField f) :=
  Computable.option_map (closed_result_computable f hf)
    (option_mapped_count_computable.comp Computable.snd)

theorem closedOrdinaryFieldEffective : ClosedOrdinaryFieldEffective := by
  intro f hf
  exact ⟨closed_result_computable f hf,closed_value_computable f hf,closed_count_computable f hf⟩

end LogicLineages.PermittedControl.FieldComparison
