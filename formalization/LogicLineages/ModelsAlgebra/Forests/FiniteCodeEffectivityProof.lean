module

public import LogicLineages.ModelsAlgebra.Forests.FiniteCodeTargets

@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.FiniteCodeEffectivityProof
open FiniteCode Primrec

private theorem allList {α β : Type*} [Primcodable α] [Primcodable β]
    {l : α → List β} {r : α → β → Prop} (hl : Primrec l) (hr : PrimrecRel r) :
    PrimrecPred (fun a => ∀ b ∈ l a, r a b) :=
  hr.swap.forall_mem_list.comp hl Primrec.id

private theorem exList {α β : Type*} [Primcodable α] [Primcodable β]
    {l : α → List β} {r : α → β → Prop} (hl : Primrec l) (hr : PrimrecRel r) :
    PrimrecPred (fun a => ∃ b ∈ l a, r a b) :=
  hr.swap.exists_mem_list.comp hl Primrec.id

private theorem allN {α : Type*} [Primcodable α]
    {n : α → ℕ} {r : α → ℕ → Prop} (hn : Primrec n) (hr : PrimrecRel r) :
    PrimrecPred (fun a => ∀ i ∈ List.range (n a), r a i) :=
  allList (list_range.comp hn) hr

private theorem allN₂ {α : Type*} [Primcodable α]
    {n : α → ℕ} {r : α → ℕ → ℕ → Prop} (hn : Primrec n)
    (hr : PrimrecPred (fun t : (α × ℕ) × ℕ => r t.1.1 t.1.2 t.2)) :
    PrimrecPred (fun a => ∀ i ∈ List.range (n a), ∀ j ∈ List.range (n a), r a i j) :=
  allN hn (allN (hn.comp fst) hr)

private theorem allN₃ {α : Type*} [Primcodable α]
    {n : α → ℕ} {r : α → ℕ → ℕ → ℕ → Prop} (hn : Primrec n)
    (hr : PrimrecPred (fun t : ((α × ℕ) × ℕ) × ℕ => r t.1.1.1 t.1.1.2 t.1.2 t.2)) :
    PrimrecPred (fun a => ∀ i ∈ List.range (n a), ∀ j ∈ List.range (n a),
      ∀ k ∈ List.range (n a), r a i j k) :=
  allN hn (allN₂ (hn.comp fst) hr)

private theorem impP {α : Type*} [Primcodable α] {p q : α → Prop}
    (hp : PrimrecPred p) (hq : PrimrecPred q) : PrimrecPred (fun a => p a → q a) :=
  (hp.not.or hq).of_eq (fun _ => by simp only [imp_iff_not_or])

private theorem iffP {α : Type*} [Primcodable α] {p q : α → Prop}
    (hp : PrimrecPred p) (hq : PrimrecPred q) : PrimrecPred (fun a => p a ↔ q a) :=
  ((impP hp hq).and (impP hq hp)).of_eq (fun _ => by simp only [iff_def])

private theorem memP {α : Type*} [Primcodable α] : PrimrecRel (fun a (l : List α) => a ∈ l) :=
  PrimrecRel.swap ((@Primrec.eq α _).exists_mem_list.of_eq (fun l a => by simp))

private theorem relP {α : Type*} [Primcodable α] {c : α → Code} {i j : α → ℕ}
    (hc : Primrec c) (hi : Primrec i) (hj : Primrec j) :
    PrimrecPred (fun a => Rel (c a) (i a) (j a)) :=
  memP.comp (hi.pair hj) (snd.comp hc)

private theorem allPairsPrim : Primrec allPairs :=
  list_flatMap list_range (list_map (list_range.comp fst) ((snd.comp fst).pair snd))

private theorem sublistsPrim {α : Type*} [Primcodable α] : Primrec (@List.sublists α) := by
  have h : Primrec (fun l : List α => l.foldr
      (fun a ih => ih.flatMap (fun x => [x, a :: x])) [[]]) :=
    list_foldr Primrec.id (const [[]])
      (list_flatMap (snd.comp snd)
        (list_cons.comp snd (list_cons.comp
          (list_cons.comp (fst.comp (snd.comp fst)) snd) (const []))).to₂).to₂
  apply h.of_eq
  intro l
  induction l with
  | nil => rfl
  | cons a l ih => simpa only [List.foldr_cons, ih, List.bind_eq_flatMap] using (List.sublists_cons a l).symm

private theorem allRelationsPrim : Primrec allRelations :=
  list_map (sublistsPrim.comp allPairsPrim) (fst.pair snd)

private theorem hostCodesPrim : Primrec hostCodes :=
  list_flatMap (list_range.comp (succ.comp Primrec.id)) (allRelationsPrim.comp snd)

private theorem mapWordsPrim : Primrec₂ mapWords := by
  have h : Primrec (fun p : ℕ × ℕ => p.1.rec (motive := fun _ => List (List ℕ)) [[]]
      (fun _ ih => (List.range p.2).flatMap (fun a => ih.map (List.cons a)))) :=
    nat_rec' fst (const [[]])
      (list_flatMap (list_range.comp (snd.comp fst))
        (list_map (snd.comp (snd.comp fst))
          (list_cons.comp (snd.comp fst) snd).to₂).to₂).to₂
  apply h.of_eq
  intro p
  rcases p with ⟨n,m⟩
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Nat.rec_add_one, mapWords, ih]

private theorem forestPredPrim : PrimrecPred ForestPredicate := by
  apply PrimrecPred.and
  · exact allList snd ((nat_lt.comp (fst.comp snd) (fst.comp fst)).and
      (nat_lt.comp (snd.comp snd) (fst.comp fst)))
  apply PrimrecPred.and
  · exact allN fst (relP fst snd snd)
  apply PrimrecPred.and
  · exact allN₂ fst (impP (relP (fst.comp fst) (snd.comp fst) snd)
      (impP (relP (fst.comp fst) snd (snd.comp fst)) (Primrec.eq.comp (snd.comp fst) snd)))
  apply PrimrecPred.and
  · exact allN₃ fst (impP (relP (fst.comp (fst.comp fst)) (snd.comp (fst.comp fst)) (snd.comp fst))
      (impP (relP (fst.comp (fst.comp fst)) (snd.comp fst) snd)
        (relP (fst.comp (fst.comp fst)) (snd.comp (fst.comp fst)) snd)))
  · exact allN₃ fst (impP (relP (fst.comp (fst.comp fst)) (snd.comp (fst.comp fst)) snd)
      (impP (relP (fst.comp (fst.comp fst)) (snd.comp fst) snd)
        ((relP (fst.comp (fst.comp fst)) (snd.comp (fst.comp fst)) (snd.comp fst)).or
         (relP (fst.comp (fst.comp fst)) (snd.comp fst) (snd.comp (fst.comp fst))))))

private theorem mapPredPrim : PrimrecPred
    (fun t : Code × Code × List ℕ => MapPredicate t.1 t.2.1 t.2.2) := by
  apply PrimrecPred.and
  · exact Primrec.eq.comp (list_length.comp (snd.comp snd)) (fst.comp fst)
  apply PrimrecPred.and
  · exact allList (snd.comp snd) (nat_lt.comp snd (fst.comp (fst.comp (snd.comp fst))))
  apply PrimrecPred.and
  · exact allN₂ (fst.comp fst) (impP
      (Primrec.eq.comp
        ((list_getD 0).comp (snd.comp (snd.comp (fst.comp fst))) (snd.comp fst))
        ((list_getD 0).comp (snd.comp (snd.comp (fst.comp fst))) snd))
      (Primrec.eq.comp (snd.comp fst) snd))
  · exact allN₂ (fst.comp fst) (iffP
      (relP (fst.comp (snd.comp (fst.comp fst)))
        ((list_getD 0).comp (snd.comp (snd.comp (fst.comp fst))) (snd.comp fst))
        ((list_getD 0).comp (snd.comp (snd.comp (fst.comp fst))) snd))
      (relP (fst.comp (fst.comp fst)) (snd.comp fst) snd))

private theorem embeddingPredPrim : PrimrecRel EmbeddingPredicate :=
  exList (mapWordsPrim.comp (fst.comp fst) (fst.comp snd))
    (mapPredPrim.comp ((fst.comp fst).pair ((snd.comp fst).pair snd)))

private theorem permittedPredPrim : PrimrecRel PermittedPredicate :=
  (forestPredPrim.comp snd).and (allList fst
    ((forestPredPrim.comp snd).and
      ((embeddingPredPrim.comp snd (snd.comp fst)).not)))

private theorem boundedPredPrim : PrimrecPred
    (fun t : List Code × Code × Code => BoundedHostPredicate t.1 t.2.1 t.2.2) :=
  exList (hostCodesPrim.comp (nat_add.comp (fst.comp (fst.comp snd)) (fst.comp (snd.comp snd))))
    ((permittedPredPrim.comp (fst.comp fst) snd).and
      ((embeddingPredPrim.comp (fst.comp (snd.comp fst)) snd).and
        (embeddingPredPrim.comp (snd.comp (snd.comp fst)) snd)))

theorem forestFiniteTestsPrimitiveRecursive : Targets.ForestFiniteTestsPrimitiveRecursive := by
  have hv : Primrec valid := forestPredPrim.decide
  have hm : Primrec (fun t : Code × Code × List ℕ => mapTest t.1 t.2.1 t.2.2) := mapPredPrim.decide
  have he : Primrec₂ embeddingTest := embeddingPredPrim.decide
  have hp : Primrec₂ permittedTest := permittedPredPrim.decide
  have hb : Primrec (fun t : List Code × Code × Code => boundedHostTest t.1 t.2.1 t.2.2) :=
    boundedPredPrim.decide
  refine ⟨Primrec.encode, Primrec.decode, allPairsPrim, allRelationsPrim, hostCodesPrim,
    mapWordsPrim, hv, hm, he, hp, hb, ?_⟩
  exact Primrec.and.comp (Primrec.and.comp (hp.comp fst (fst.comp snd))
    (hp.comp fst (snd.comp snd))) (Primrec.not.comp hb)

end LogicLineages.ModelsAlgebra.Forests.FiniteCodeEffectivityProof
