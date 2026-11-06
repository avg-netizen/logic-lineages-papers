module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.Targets
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.WordAlgebraProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadDerivedProof

theorem graph_iff (h : Targets.HeadGraphExact) (code : Nat) (hc : ValidHead code)
    (n y : Nat) : HeadGraph code n y ↔ y = headValue code n := by
  obtain ⟨hd, he⟩ := (h code hc).2 n
  simp only [HeadGraph, graphCutoff, graphExceptions, Nat.zero_le, true_and,
    List.not_mem_nil, false_and, exists_false, or_false]
  rw [he]
  constructor
  · rintro ⟨_, hy⟩
    omega
  · intro hy
    subst y
    exact ⟨hd, rfl⟩

theorem headGraphTotalFunctional (h : Targets.HeadGraphExact) :
    Targets.HeadGraphTotalFunctional := by
  intro code hc
  refine ⟨rfl, rfl, graph_iff h code hc, ?_⟩
  intro n
  exact ⟨headValue code n, (graph_iff h code hc n _).mpr rfl,
    fun y hy => (graph_iff h code hc n y).mp hy⟩

theorem headEquation_allowed {D code input output : Nat}
    (h : UnaryAllowed D (headRow code)) :
    RowAllowed D (headEquation code input output) := by
  intro a ha
  change a ∈ (2,output,[]) ::
    (headRow code).2.map (fun b => (-b.1,input,b.2)) at ha
  rcases List.mem_cons.mp ha with rfl | ha
  · intro b hb
    exact False.elim (List.not_mem_nil hb)
  · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact h b hb

theorem headEquation_domain {code input output : Nat} (ν : Nat → Nat)
    (h : UnaryDomain (headRow code) (ν input)) :
    RowDomain (headEquation code input output) ν := by
  intro a ha
  change a ∈ (2,output,[]) ::
    (headRow code).2.map (fun b => (-b.1,input,b.2)) at ha
  rcases List.mem_cons.mp ha with rfl | ha
  · trivial
  · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact h b hb

theorem headEquation_value (code input output : Nat) (ν : Nat → Nat) :
    RowValue (headEquation code input output) ν =
      2*(ν output : Int) - unaryValue (headRow code) (ν input) := by
  have hneg : ∀ ls : List (Int × Word),
      (ls.map (fun a => -a.1 * (wordValue a.2 (ν input) : Int))).sum =
        -(ls.map (fun a => a.1 * (wordValue a.2 (ν input) : Int))).sum := by
    intro ls
    induction ls with
    | nil => simp
    | cons a ls ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        simp only [neg_mul, neg_add_rev]
        omega
  simp only [headEquation, RowValue, unaryValue, List.map_cons, List.sum_cons,
    List.map_map, Function.comp_def, wordValue]
  rw [hneg]
  omega

theorem headEquationExact (h : Targets.HeadGraphExact) : Targets.HeadEquationExact := by
  intro code hc input output
  refine ⟨headEquation_allowed (h code hc).1, ?_⟩
  intro ν
  obtain ⟨hd, he⟩ := (h code hc).2 (ν input)
  refine ⟨headEquation_domain ν hd, ?_⟩
  rw [headEquation_value, he]
  omega

theorem member_norm_le_sum (codes : List Nat) (code : Nat) (hc : code ∈ codes) :
    rawNormCode code ≤ (codes.map rawNormCode).sum := by
  induction codes with
  | nil => exact False.elim (List.not_mem_nil hc)
  | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hc with rfl | hc
      · omega
      · have hi := ih hc
        omega

theorem family_degree (codes : List Nat) : 3 ≤ familyDegree codes := by
  unfold familyDegree
  omega

theorem head_degree_le_family {codes : List Nat} {code : Nat} (hc : code ∈ codes) :
    headDegree code ≤ familyDegree codes := by
  have hl := member_norm_le_sum codes code hc
  unfold headDegree familyDegree
  omega

theorem finiteFamilyDegree (h : Targets.HeadGraphExact) : Targets.FiniteFamilyDegree := by
  intro codes hc
  refine ⟨family_degree codes, ?_⟩
  intro code hcode
  exact WordAlgebraProof.unaryAllowed_mono (head_degree_le_family hcode)
    (headRow code) (h code (hc code hcode)).1

end LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadDerivedProof
