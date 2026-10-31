module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarReconstructTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarReconstruct.Proof
open CotreeGrammarFlow CotreeGrammarOpen CotreeGrammarForest CotreeGrammarNormal
open CotreeGrammarRanks CotreeGrammarConnected
open CotreeGrammarOpen.Proof CotreeGrammarForest.Proof

variable {Q : Type} [DecidableEq Q] {δ : Q → Q → Q}

theorem rankSum_perm (rank : Q → Nat) {F G : List (Packed δ)} (h : F.Perm G) :
    rankSum rank F = rankSum rank G := (h.map _).sum_eq

theorem rankSum_cons (rank : Q → Nat) (t : Packed δ) (F : List (Packed δ)) :
    rankSum rank (t::F) = rank t.1 + rankSum rank F := by simp [rankSum]

theorem positive_member (F : List (Packed δ)) (p : Q × Q)
    (h : 0 < (forestCounts F).binary p) : ∃ t ∈ F, 0 < (counts t.2).binary p := by
  induction F with
  | nil => simp [forestCounts] at h
  | cons t F ih =>
    change 0 < (counts t.2).binary p + (forestCounts F).binary p at h
    by_cases ht : 0 < (counts t.2).binary p
    · exact ⟨t,List.mem_cons_self,ht⟩
    · have hf : 0 < (forestCounts F).binary p := by omega
      rcases ih hf with ⟨u,hu,hp⟩
      exact ⟨u,List.mem_cons_of_mem _ hu,hp⟩

theorem minimal_normal (c : Counts Q) (G : List (Packed δ)) (hG : forestCounts G = c)
    (hmin : ∀ H : List (Packed δ), forestCounts H = c → G.length ≤ H.length) :
    NoCrossHole G ∧ NoBareHole G := by
  classical
  constructor
  · intro a ta b tb rest hp hm
    obtain ⟨C,rfl⟩ := (CotreeGrammarOpen.StatementChecks.holeFactorization Q δ a ta b).mp hm
    have hc : forestCounts (⟨a,plug C tb⟩ :: rest) = c :=
      (merge_counts C tb rest).trans ((counts_perm hp).symm.trans hG)
    have hle := hmin _ hc
    have hl := hp.length_eq
    simp only [List.length_cons] at hle hl
    omega
  · intro q hq
    have hp := List.perm_cons_erase hq
    have hc : forestCounts (G.erase ⟨q,Tree.hole q⟩) = c :=
      (remove_hole_counts q _).trans ((counts_perm hp).symm.trans hG)
    have hle := hmin _ hc
    have hl := hp.length_eq
    simp only [List.length_cons] at hl
    omega

variable [Fintype Q]

theorem nonbare_positive {q} (t : Tree δ q) (h : t ≠ .hole q) :
    0 < consumed δ (counts t) q := by
  cases t with
  | hole => exact (h rfl).elim
  | terminal B q hq =>
    have he := (CotreeGrammarFlow.Proof.leaf_realizes δ B q hq).2.2 q
    simp only [if_true] at he
    change 0 < consumed δ (CotreeGrammarFlow.Proof.leafCounts B q) q
    omega
  | @branch r s l u =>
    rw [counts,CotreeGrammarFlow.Proof.node_consumed]
    simp only [if_true]
    omega

theorem cycle_impossible (root : Q) (c : Counts Q) (rank : Q → Nat) (G : List (Packed δ))
    (hRank : RankedSupport δ root c rank) (hG : forestCounts G = c)
    (hmin : ∀ H : List (Packed δ), forestCounts H = c → G.length ≤ H.length)
    (hrmin : ∀ H : List (Packed δ), forestCounts H = c → H.length = G.length →
      rankSum rank G ≤ rankSum rank H) (hnb : NoBareHole G)
    {x : Q} (t : Tree δ x) (rest : List (Packed δ))
    (hp : G.Perm (⟨x,t⟩::rest)) (ht : holes t = [x]) (hx : x ≠ root) : False := by
  classical
  have hmem : (⟨x,t⟩ : Packed δ) ∈ G := hp.mem_iff.mpr List.mem_cons_self
  have hnon : t ≠ .hole x := by intro he; subst t; exact hnb x hmem
  have hlocal := nonbare_positive t hnon
  have hsplit : c = addCounts (counts t) (forestCounts rest) :=
    hG.symm.trans ((counts_perm hp).trans (counts_cons _ _))
  have hused : 0 < consumed δ c x := by rw [hsplit,consumed_add]; omega
  rcases hRank.2 x hx with ⟨hz,_⟩ | ⟨_,y,hy,hxy,hedge⟩
  · omega
  · rcases hedge with ⟨r,s,hpos,hhead,hchild⟩
    have hc : c.binary (r,s) = (counts t).binary (r,s) + (forestCounts rest).binary (r,s) :=
      congrArg (fun c => c.binary (r,s)) hsplit
    by_cases hinside : 0 < (counts t).binary (r,s)
    · obtain ⟨v,hvholes,hvcounts⟩ :=
        CotreeGrammarProduction.StatementChecks.cycleRotateProduction Q δ x t r s ht hinside hchild
      have hnew : forestCounts (⟨δ r s,v⟩::rest) = c := by
        rw [counts_cons,hvcounts]
        exact (counts_cons ⟨x,t⟩ rest).symm.trans ((counts_perm hp).symm.trans hG)
      have hlen : (⟨δ r s,v⟩::rest : List (Packed δ)).length = G.length := by
        simpa only [List.length_cons] using hp.length_eq.symm
      have hle := hrmin _ hnew hlen
      have hsum := rankSum_perm rank hp
      rw [rankSum_cons] at hsum hle
      change rankSum rank G = rank x + rankSum rank rest at hsum
      change rankSum rank G ≤ rank (δ r s) + rankSum rank rest at hle
      rw [hhead] at hle
      omega
    · have hout : 0 < (forestCounts rest).binary (r,s) := by omega
      obtain ⟨u,hu,hprod⟩ := positive_member rest (r,s) hout
      have hpU := List.perm_cons_erase hu
      have hp2 := hp.trans (hpU.cons ⟨x,t⟩)
      obtain ⟨v,hvcounts,_⟩ :=
        CotreeGrammarInsertion.StatementChecks.cycleInsertProduction Q δ x u.1 t u.2 r s ht hprod hchild
      have hnew : forestCounts (⟨u.1,v⟩ :: rest.erase u) = c := by
        calc
          _ = addCounts (addCounts (counts u.2) (counts t)) (forestCounts (rest.erase u)) := by
            rw [counts_cons,hvcounts]
          _ = forestCounts (⟨x,t⟩::u::rest.erase u) := by
            rw [counts_cons,counts_cons]
            apply countExt <;> intro p <;> simp only [addCounts] <;> omega
          _ = c := (counts_perm hp2).symm.trans hG
      have hle := hmin _ hnew
      have hlen := hp2.length_eq
      simp only [List.length_cons] at hle hlen
      omega

theorem forestReconstruction : Targets.ForestReconstruction := by
  intro Q _ _ δ root w F rank hR hRank
  classical
  let c := forestCounts F
  have hex : ∃ n, ∃ G : List (Packed δ), forestCounts G = c ∧ G.length = n :=
    ⟨F.length,F,rfl,rfl⟩
  obtain ⟨G0,hG0,hl0⟩ := Nat.find_spec hex
  have hexrank : ∃ n, ∃ G : List (Packed δ), forestCounts G = c ∧
      G.length = Nat.find hex ∧ rankSum rank G = n :=
    ⟨rankSum rank G0,G0,hG0,hl0,rfl⟩
  obtain ⟨G,hG,hlen,hsum⟩ := Nat.find_spec hexrank
  have hmin : ∀ H : List (Packed δ), forestCounts H = c → G.length ≤ H.length := by
    intro H hH
    rw [hlen]
    exact Nat.find_min' hex ⟨H,hH,rfl⟩
  have hrmin : ∀ H : List (Packed δ), forestCounts H = c → H.length = G.length →
      rankSum rank G ≤ rankSum rank H := by
    intro H hH hL
    rw [hsum]
    exact Nat.find_min' hexrank ⟨H,hH,hL.trans hlen,rfl⟩
  have hnormal := minimal_normal c G hG hmin
  have hRG : Realizes δ root w (forestCounts G) := by rw [hG]; exact hR
  have hbalance := CotreeGrammarNormal.StatementChecks.realizedBalance Q δ root w G hRG
  obtain ⟨t,rest,hp,hclosed,hcycles,_⟩ :=
    CotreeGrammarNormal.StatementChecks.normalStructure Q δ root G hbalance hnormal.1
  have hempty : rest = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro u hu
    have humem : u ∈ G := hp.mem_iff.mpr (List.mem_cons_of_mem _ hu)
    have hpU := List.perm_cons_erase humem
    exact cycle_impossible root c rank G hRank hG hmin hrmin hnormal.2 u.2 _ hpU
      (hcycles u hu).2 (hcycles u hu).1
  subst rest
  refine ⟨t,hclosed,?_⟩
  have he : forestCounts G = counts t := by
    rw [counts_perm hp,counts_cons,counts_nil]
    apply countExt <;> intro p <;> simp [addCounts,zeroCounts]
  exact he.symm.trans hG

theorem wordReconstruction : Targets.WordReconstruction := by
  intro Q _ _ δ root w F hR hc
  obtain ⟨rank,hRank⟩ := (CotreeGrammarRanks.StatementChecks.rankReachabilityExact Q δ root _).mpr hc
  obtain ⟨t,hclosed,hcounts⟩ := forestReconstruction Q δ root w F rank hR hRank
  refine ⟨word t,CotreeGrammarOpen.StatementChecks.closedBuilds Q δ root t hclosed,?_⟩
  apply List.perm_iff_count.mpr
  intro B
  calc
    (word t).count B = terminalTotal (counts t) B :=
      ((CotreeGrammarOpen.StatementChecks.treeTerminals Q δ root t).1 B).symm
    _ = terminalTotal (forestCounts F) B := congrArg (fun c => terminalTotal c B) hcounts
    _ = w.count B := hR.2.1 B

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarReconstruct.Proof
