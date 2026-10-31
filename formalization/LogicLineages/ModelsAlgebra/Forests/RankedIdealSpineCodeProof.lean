module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealSpineCodeTargets
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealSpineStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularCodeStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealSpineCode.Proof
open RankedParse RankedIdealRank RankedIdealComponents RankedIdealCompletion RankedIdealRegularCode RankedGraphImage RankedIdealSpine RankedIdealContext
 theorem ops_mem (o : Operation) : o ∈ ops := by cases o <;> simp [ops]
 theorem frame_mem (C : Code) q r : r ∈ frames C q ↔
    ∃ o x y, (leftOK C q o x y ∧ r = ⟨o,true,component C y⟩) ∨
      (rightOK C q o x y ∧ r = ⟨o,false,component C x⟩) := by
  simp [frames, C.complete, ops_mem]
 theorem seed_mem (C : Code) q rec B : B ∈ seeds C q rec ↔
    (SameComponent C.machine q C.machine.leaf ∧ B = atom) ∨
    (∃ p, Lower C.machine p q ∧ B ∈ rec p) ∨
    ∃ o x y, nodeOK C q o x y ∧ ∃ A ∈ rec x, ∃ D ∈ rec y, product o A D = B := by
  simp [seeds, C.complete, ops_mem, List.mem_flatMap, List.mem_map, or_assoc]
 theorem allowed_list (rs : List Rule) c :
    RankedIdealRegular.allowed (fun i : Fin rs.length => viewRule (rs[i])) c ↔
    ∃ r ∈ rs, ∃ t, language r.side t ∧
      c = if r.holeLeft then .left r.op .hole t else .right r.op t .hole := by
  constructor
  · rintro ⟨i,t,ht,hc⟩
    exact ⟨rs[i], List.getElem_mem _, t, ht, hc⟩
  · rintro ⟨r,hr,t,ht,hc⟩
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hr
    refine ⟨⟨i,hi⟩, t, ?_, ?_⟩
    · change language (rs[i]).side t
      rw [he]
      exact ht
    · change c = if (rs[i]).holeLeft then .left (rs[i]).op .hole t else .right (rs[i]).op t .hole
      rw [he]
      exact hc
 theorem framesExact : Targets.FramesExact := by
  intro C q c
  change (RankedIdealRegular.allowed _ c) ↔ _
  rw [allowed_list]
  constructor
  · rintro ⟨r,hr,t,ht,hc⟩
    obtain ⟨o,x,y,h⟩ := (frame_mem C q r).mp hr
    rcases h with ⟨h,rfl⟩ | ⟨h,rfl⟩
    · simp only [Bool.true_eq, ↓reduceIte] at hc
      subst c
      exact .left h.2.2.2.1 h.2.2.2.2 h.2.2.1 h.1 h.2.1
        ((RankedIdealRegularCode.StatementChecks.componentExact C y t).mp ht)
    · simp only [Bool.false_eq_true, ↓reduceIte] at hc
      subst c
      exact .right h.2.2.2.1 h.2.2.2.2 h.2.2.1 h.1 h.2.1
        ((RankedIdealRegularCode.StatementChecks.componentExact C x t).mp ht)
  · intro h
    cases h with
    | @left o x y r hx hy ho px py hr =>
        refine ⟨⟨o,true,component C y⟩, ?_, r, ?_, rfl⟩
        · exact (frame_mem C q _).mpr ⟨o,x,y,Or.inl ⟨⟨px,py,ho,hx,hy⟩,rfl⟩⟩
        · exact (RankedIdealRegularCode.StatementChecks.componentExact C y r).mpr hr
    | @right o x y l hx hy ho px py hl =>
        refine ⟨⟨o,false,component C x⟩, ?_, l, ?_, rfl⟩
        · exact (frame_mem C q _).mpr ⟨o,x,y,Or.inr ⟨⟨px,py,ho,hx,hy⟩,rfl⟩⟩
        · exact (RankedIdealRegularCode.StatementChecks.componentExact C x l).mpr hl
 theorem seedsIdeal : Targets.SeedsIdeal := by
  intro C q rec h B hB
  rcases (seed_mem C q rec B).mp hB with ⟨_,rfl⟩ | ⟨p,hp,hB⟩ | ⟨o,x,y,hxy,A,hA,D,hD,rfl⟩
  · exact RankedIdealRegularCode.StatementChecks.atomIdeal
  · exact (h p hp).1 B hB
  · exact RankedIdealRegularCode.StatementChecks.productIdeal o A D
      ((h x hxy.2.2.2.1).1 A hA) ((h y hxy.2.2.2.2).1 D hD)
 theorem seedsSound : Targets.SeedsSound := by
  intro C q rec h B hB t ht
  rcases (seed_mem C q rec B).mp hB with ⟨hc,rfl⟩ | ⟨p,hp,hB⟩ | ⟨o,x,y,hxy,A,hA,D,hD,rfl⟩
  · have he := (RankedIdealRegularCode.StatementChecks.atomExact t).mp ht
    subst t
    exact RankedIdealSpine.StatementChecks.entrySound C.machine q _ (.atom hc)
  · exact RankedIdealSpine.StatementChecks.entrySound C.machine q _
      (.lower hp ((h p hp).2 t |>.mp ⟨B,hB,ht⟩))
  · obtain ⟨u,⟨l,r,hl,hr,rfl⟩,htu⟩ :=
      (RankedIdealRegularCode.StatementChecks.productExact o A D t).mp ht
    have hlx := ((h x hxy.2.2.2.1).2 l).mp ⟨A,hA,hl⟩
    have hry := ((h y hxy.2.2.2.2).2 r).mp ⟨D,hD,hr⟩
    have hn := RankedIdealSpine.StatementChecks.entrySound C.machine q _
      (.node hxy.2.2.2.1 hxy.2.2.2.2 hxy.2.2.1 hxy.1 hxy.2.1 hlx hry)
    exact RankedIdealComponents.StatementChecks.stateLanguageDownward C.machine q _ _ htu hn
 theorem entriesCovered : Targets.EntriesCovered := by
  intro C q rec h t ht
  cases ht with
  | atom hc =>
      exact ⟨atom,(seed_mem C q rec atom).mpr (Or.inl ⟨hc,rfl⟩),
        (RankedIdealRegularCode.StatementChecks.atomExact _).mpr rfl⟩
  | @lower p t hp hr =>
      obtain ⟨B,hB,hBt⟩ := ((h p hp).2 t).mpr hr
      exact ⟨B,(seed_mem C q rec B).mpr (Or.inr (Or.inl ⟨p,hp,hB⟩)),hBt⟩
  | @node o x y l r hx hy ho px py hl hr =>
      obtain ⟨A,hA,hAl⟩ := ((h x hx).2 l).mpr hl
      obtain ⟨D,hD,hDr⟩ := ((h y hy).2 r).mpr hr
      refine ⟨product o A D,(seed_mem C q rec _).mpr
        (Or.inr (Or.inr ⟨o,x,y,⟨px,py,ho,hx,hy⟩,A,hA,D,hD,rfl⟩)), ?_⟩
      exact (RankedIdealRegularCode.StatementChecks.productExact o A D _).mpr
        ⟨.node o l r,⟨l,r,hAl,hDr,rfl⟩,RankedIdealContext.Proof.embeddingReflexive _⟩
end LogicLineages.ModelsAlgebra.Forests.RankedIdealSpineCode.Proof
