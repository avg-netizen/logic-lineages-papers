module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowRegistryDecoder
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryTupleProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowRegistryDecoderProof
open GorbowRegistryTuple GorbowRegistryDecoder

private theorem candidateMember (code a b : Nat) (ha : a≤code) (hb : b≤code) :
    (a,b) ∈ pairCandidates code := by
  simp only [pairCandidates,List.mem_flatMap]
  exact ⟨a,List.mem_range.mpr (by omega),List.mem_map.mpr ⟨b,List.mem_range.mpr (by omega),rfl⟩⟩

theorem pairExact : Comparators.GorbowRegistryDecoder.PairExact := by
  intro code a b
  constructor
  · intro h
    have hp : decide (pair a b=code)=true := List.find?_some (p := fun p : Nat × Nat => decide (pair p.1 p.2=code)) h
    exact of_decide_eq_true hp
  · intro he
    have hm := candidateMember code a b (by rw [← he]; exact (GorbowRegistryTupleProof.bounds.1 a b).1)
      (by rw [← he]; exact (GorbowRegistryTupleProof.bounds.1 a b).2)
    cases hd : decodePair code with
    | none =>
      have hn := List.find?_eq_none.mp hd
      exact False.elim (hn (a,b) hm (by simpa using he))
    | some p =>
      have hp : pair p.1 p.2=code := by
        have hx : decide (pair p.1 p.2=code)=true := List.find?_some (p := fun q : Nat × Nat => decide (pair q.1 q.2=code)) hd
        exact of_decide_eq_true hx
      have heq := (GorbowRegistryTupleProof.pairInjection _ _ _ _).mp (hp.trans he.symm)
      have hpab : p=(a,b) := Prod.ext heq.1 heq.2
      simp [hpab]

private theorem encodedPair (a b : Nat) : decodePair (pair a b)=some (a,b) := (pairExact _ _ _).mpr rfl

theorem stepInvariant : Comparators.GorbowRegistryDecoder.StepInvariant := by
  refine ⟨fun _ => rfl,?_⟩
  intro c acc next h
  cases c with
  | zero =>
    have he : (0,acc)=next := by simpa [tupleStep] using h
    subst next
    exact ⟨rfl,Or.inl rfl⟩
  | succ c =>
    cases hd : decodePair c with
    | none => simp [tupleStep,hd] at h
    | some p =>
      obtain ⟨a,b⟩ := p
      have hn : (b,a::acc)=next := by simpa [tupleStep,hd] using h
      subst next
      have he := (pairExact c a b).mp hd
      refine ⟨?_,Or.inr ?_⟩
      · simp [restore,List.foldl,he]
      · have hb := (GorbowRegistryTupleProof.bounds.1 a b).2
        omega

private theorem zeroStable (acc : List Nat) (fuel : Nat) :
    tupleStep^[fuel] (some (0,acc))=some (0,acc) := Function.iterate_fixed rfl fuel
private theorem noneStable (fuel : Nat) : tupleStep^[fuel] none=none := Function.iterate_fixed rfl fuel

theorem fuelSufficiency : Comparators.GorbowRegistryDecoder.FuelSufficiency := by
  intro xs
  induction xs with
  | nil => intro acc fuel _; simpa [tuple] using zeroStable acc fuel
  | cons a xs ih =>
    intro acc fuel hf
    cases fuel with
    | zero => simp [tuple] at hf
    | succ fuel =>
      have ht := GorbowRegistryTupleProof.bounds.2 a xs
      have hf' : tuple xs≤fuel := by omega
      rw [Function.iterate_succ_apply]
      simp only [tuple,tupleStep,encodedPair,Option.bind_some,pure]
      change tupleStep^[fuel] (some (tuple xs,a::acc)) = _
      rw [ih (a::acc) fuel hf']
      simp [List.reverse_cons,List.append_assoc]

private theorem restoreTuple (acc xs : List Nat) : restore acc (tuple xs)=tuple (acc.reverse++xs) := by
  induction acc generalizing xs with
  | nil => rfl
  | cons a acc ih =>
    change restore acc (tuple (a::xs)) = _
    rw [ih]
    simp [List.reverse_cons,List.append_assoc]
private theorem restoreZero (acc : List Nat) : restore acc 0=tuple acc.reverse := by
  simpa [tuple] using restoreTuple acc []
private theorem iterateRestore (fuel c : Nat) (acc : List Nat) (next : Nat × List Nat)
    (h : tupleStep^[fuel] (some (c,acc))=some next) : restore next.2 next.1=restore acc c := by
  induction fuel generalizing c acc with
  | zero => cases h; rfl
  | succ fuel ih =>
    rw [Function.iterate_succ_apply] at h
    cases hs : tupleStep (some (c,acc)) with
    | none => simp [hs,noneStable] at h
    | some p =>
      have hr := ih p.1 p.2 (by simpa [hs] using h)
      exact hr.trans (stepInvariant.2 c acc p hs).1

theorem tupleExact : Comparators.GorbowRegistryDecoder.TupleExact := by
  intro code xs
  constructor
  · intro h
    cases hs : tupleStep^[code] (some (code,[])) with
    | none => simp [decodeTuple,hs] at h
    | some p =>
      obtain ⟨rest,acc⟩ := p
      by_cases hz : rest=0
      · subst rest
        have hx : acc.reverse=xs := by simpa [decodeTuple,hs] using h
        have hr := iterateRestore code code [] (0,acc) hs
        change restore acc 0=code at hr
        rw [restoreZero,hx] at hr
        exact hr
      · simp [decodeTuple,hs,hz] at h
  · intro he
    subst code
    have h := fuelSufficiency xs [] (tuple xs) (le_refl _)
    simp [decodeTuple,h]

theorem headerExact : Comparators.GorbowRegistryDecoder.HeaderExact := by
  intro code arity tag args
  constructor
  · intro h
    cases ha : decodePair code with
    | none => simp [decodeHeader,ha] at h
    | some p =>
      obtain ⟨a,body⟩ := p
      cases ht : decodePair body with
      | none => simp [decodeHeader,ha,ht] at h
      | some p =>
        obtain ⟨t,c⟩ := p
        cases hc : decodeTuple c with
        | none => simp [decodeHeader,ha,ht,hc] at h
        | some xs =>
          have he : a=arity ∧ t=tag ∧ xs=args := by simpa [decodeHeader,ha,ht,hc] using h
          obtain ⟨rfl,rfl,rfl⟩ := he
          have hab := (pairExact _ _ _).mp ha
          have htc := (pairExact _ _ _).mp ht
          have hxs := (tupleExact _ _).mp hc
          simpa [header,← htc,← hxs] using hab
  · intro h
    subst code
    have ht := (tupleExact (tuple args) args).mpr rfl
    simp [decodeHeader,header,encodedPair,ht]

private theorem pr_candidatesInner : Primrec (fun p : Nat × Nat =>
    (List.range (p.1+1)).map (fun b => (p.2,b))) :=
  Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst))
    ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂
private theorem pr_pairCandidates : Primrec pairCandidates :=
  Primrec.list_flatMap (Primrec.list_range.comp Primrec.succ) pr_candidatesInner.to₂
private theorem pr_pairPredicate : Primrec (fun p : Nat × Nat × Nat => decide (pair p.2.1 p.2.2=p.1)) :=
  (Primrec.eq.comp (GorbowRegistryTupleProof.uniformPrograms.1.comp Primrec.snd) Primrec.fst).decide
private theorem pr_decodePair : Primrec decodePair := by
  have hi := Primrec.list_findIdx pr_pairCandidates pr_pairPredicate.to₂
  have h := Primrec.list_getElem?.comp pr_pairCandidates hi
  exact h.of_eq (fun c => (List.find?_eq_getElem?_findIdx).symm)
private theorem pr_positiveStep : Primrec (fun p : Nat × List Nat =>
    (decodePair (p.1-1)).bind (fun q => some (q.2,q.1::p.2))) := by
  have hl : Primrec (fun p : (Nat × List Nat) × Nat × Nat => some (p.2.2,p.2.1::p.1.2)) :=
    Primrec.option_some.comp ((Primrec.snd.comp Primrec.snd).pair
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)))
  exact Primrec.option_bind (pr_decodePair.comp (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1))) hl.to₂
private theorem pr_someStep : Primrec (fun p : Nat × List Nat => tupleStep (some p)) := by
  have h := Primrec.ite (Primrec.eq.comp (Primrec.fst : Primrec (fun p : Nat × List Nat => p.1)) (Primrec.const 0))
    (Primrec.option_some.comp Primrec.id) pr_positiveStep
  exact h.of_eq (fun p => by rcases p with ⟨c,acc⟩; cases c <;> simp [tupleStep])
private theorem pr_tupleStep : Primrec tupleStep := by
  have h := Primrec.option_bind (Primrec.id : Primrec (fun s : State => s)) (pr_someStep.comp Primrec.snd).to₂
  exact h.of_eq (fun s => by cases s <;> rfl)
private theorem pr_iteration : Primrec (fun c : Nat => tupleStep^[c] (some (c,([] : List Nat)))) :=
  Primrec.nat_iterate Primrec.id (Primrec.option_some.comp (Primrec.id.pair (Primrec.const [])))
    (pr_tupleStep.comp Primrec.snd).to₂
private theorem pr_finish : Primrec (fun p : Nat × (Nat × List Nat) =>
    if p.2.1=0 then some p.2.2.reverse else none) :=
  Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0))
    (Primrec.option_some.comp (Primrec.list_reverse.comp (Primrec.snd.comp Primrec.snd))) (Primrec.const none)
private theorem pr_decodeTuple : Primrec decodeTuple := Primrec.option_bind pr_iteration pr_finish.to₂
private theorem pr_headerInner : Primrec (fun p : Nat × (Nat × Nat) × (Nat × Nat) =>
    (decodeTuple p.2.2.2).map (fun args => (p.2.1.1,p.2.2.1,args))) := by
  have hf : Primrec (fun p : (Nat × (Nat × Nat) × (Nat × Nat)) × List Nat =>
      (p.1.2.1.1,p.1.2.2.1,p.2)) :=
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd)
  exact Primrec.option_map (pr_decodeTuple.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) hf.to₂
private theorem pr_headerMiddle : Primrec (fun p : Nat × (Nat × Nat) => do
    let q ← decodePair p.2.2
    let args ← decodeTuple q.2
    pure (p.2.1,q.1,args)) := by
  have h := Primrec.option_bind (pr_decodePair.comp (Primrec.snd.comp Primrec.snd))
    (pr_headerInner.comp ((Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))).to₂
  exact h.of_eq (fun p => by
    cases ha : decodePair p.2.2 with
    | none => simp [ha]
    | some q => cases hb : decodeTuple q.2 <;> simp [ha,hb])
private theorem pr_decodeHeader : Primrec decodeHeader := Primrec.option_bind pr_decodePair pr_headerMiddle.to₂

theorem uniformPrograms : Comparators.GorbowRegistryDecoder.UniformPrograms :=
  ⟨pr_pairCandidates,pr_decodePair,pr_tupleStep,pr_decodeTuple,pr_decodeHeader⟩

theorem gorbowRegistryDecoder : Comparators.GorbowRegistryDecoder.Target :=
  ⟨pairExact,stepInvariant,fuelSufficiency,tupleExact,headerExact,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowRegistryDecoderProof
