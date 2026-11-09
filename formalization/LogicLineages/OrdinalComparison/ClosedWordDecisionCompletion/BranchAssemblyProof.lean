module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.PrefixProof
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.CommonTailProof
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.ResidueAdapterProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportMatrixProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchProof
open PolynomialGraphCompletion WordLinearDecisionCompletion RankedWordDecisionCompletion

/-- The actual accepted matrix compiler is bound internally. -/
theorem actual_matrix (D maximum : Nat) (p : Formula)
    (hD : 3 ≤ D) (hp : Formula.allowed D p) :
    OutcomeTransport.MatrixCorrect D maximum (residue p) (matrix D maximum p) :=
  OutcomeTransportProof.exactActualMatrix D maximum (residue p) hD
    (ResidueAdapterProof.residue_allowed D p hp)
    (ResidueAdapterProof.residue_congruences_linear maximum p)

theorem high_body_syntax (D N maximum : Nat) (p q : Formula)
    (hD : 3 ≤ D) (hp : Formula.allowed D p) (hmaximum : maximum ∈ names p)
    (hq : q ∈ (matrix D maximum p).cases) :
    Formula.allowed D (.conj (frame N maximum (names p)) q) ∧
    linear maximum (.conj (frame N maximum (names p)) q) = true ∧
    FormulaNamesFrom p.variables (.conj (frame N maximum (names p)) q) := by
  have hc := (actual_matrix D maximum p hD hp).1 q hq
  have hnames : FormulaNamesFrom p.variables q := by
    rw [← ResidueAdapterProof.residue_variables p]
    exact hc.2.2
  exact ⟨OutcomeTransportProof.transport_allowed_conj D _ _
      (frame_allowed D N maximum (names p)) hc.1,
    OutcomeTransportProof.transport_linear_conj maximum _ _
      (frame_linear N maximum maximum (names p)) hc.2.1,
    OutcomeTransportProof.transport_names_conj p.variables _ _
      (fun i hi => List.mem_dedup.mp (frame_names N maximum (names p) hmaximum i hi)) hnames⟩

/- Keep actual supplier programs opaque during membership/elimination inference.
Their accepted correctness theorems, rather than their implementations, are used. -/
attribute [local irreducible] matrix commonTail WordLinearDecisionCompletion.eliminate

theorem high_child_syntax (D N : Nat) (p : Formula) (hD : 3 ≤ D)
    (hp : Formula.allowed D p) (b : Branch) (hb : b ∈ highChildren D N p) :
    b.1 = N ∧ Formula.allowed D b.2 ∧
    (∃ x ∈ names p, ∀ i ∈ b.2.variables, i ≠ x ∧ i ∈ p.variables) ∧
    (names b.2).length < (names p).length := by
  obtain ⟨maximum,hmaximum,hb⟩ := List.mem_flatMap.mp hb
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hb
  have hs := high_body_syntax D N maximum p q hD hp hmaximum hq
  have hn : ∀ i ∈ (WordLinearDecisionCompletion.eliminate maximum
      (.conj (frame N maximum (names p)) q)).variables, i ≠ maximum ∧ i ∈ p.variables := by
    intro i hi
    have hh := (WordLinearDecisionCompletion.Proof.exactOutputVariables maximum _ hs.2.1 i).mp hi
    exact ⟨hh.1,hs.2.2 i hh.2⟩
  exact ⟨rfl,WordLinearDecisionCompletion.Proof.exactDegreePreservation D maximum _ hs.2.1 hs.1,
    ⟨maximum,hmaximum,hn⟩,strict_name_decrease p _ maximum hmaximum hn⟩

theorem actualChildSyntax : BranchTargets.ActualChildSyntax := by
  intro D floor p hD hp b hb
  change b ∈ prefixChildren floor (commonTail D floor p) p ++
    highChildren D (commonTail D floor p) p at hb
  rcases List.mem_append.mp hb with hb | hb
  · have h := prefix_child_syntax D floor (commonTail D floor p) p hp b hb
    exact ⟨by rw [h.1],h.2⟩
  · have h := high_child_syntax D (commonTail D floor p) p hD hp b hb
    exact ⟨by rw [h.1]; exact floor_le_commonTail D floor p,h.2⟩

theorem region_at_matrix_tail (D floor maximum : Nat) (p : Formula) (ν : Nat → Nat)
    (hmaximum : maximum ∈ names p)
    (hregion : Region (commonTail D floor p) maximum p.variables ν) :
    Region (matrix D maximum p).tail maximum (residue p).variables ν := by
  rw [ResidueAdapterProof.residue_variables]
  intro i hi
  exact ⟨(matrix_le_commonTail D floor p maximum hmaximum).trans (hregion i hi).1,
    (hregion i hi).2⟩

theorem paid_original_residue (D floor : Nat) (p : Formula) (ν : Nat → Nat)
    (hp : Formula.allowed D p) (hlarge : ∀ i ∈ p.variables, commonTail D floor p ≤ ν i) :
    Formula.meaningful p ν ∧ Formula.meaningful (residue p) ν ∧
    (Formula.eval ν (residue p) ↔ Formula.eval ν p) := by
  apply ResidueAdapterProof.exactResidueSemantics D p hp ν
  intro i hi
  exact max_le ((original_le_commonTail D floor p).trans (hlarge i hi))
    ((residue_le_commonTail D floor p).trans (hlarge i hi))

theorem high_child_sound (D floor : Nat) (p : Formula) (hD : 3 ≤ D)
    (hp : Formula.allowed D p) (b : Branch)
    (hb : b ∈ highChildren D (commonTail D floor p) p)
    (htrue : SatisfiableAt b.1 b.2) : SatisfiableAt floor p := by
  obtain ⟨maximum,hmaximum,hb⟩ := List.mem_flatMap.mp hb
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hb
  rcases htrue with ⟨ν,hfloor,hdomains,htrue⟩
  have hs := high_body_syntax D (commonTail D floor p) maximum p q hD hp hmaximum hq
  obtain ⟨n,hdomains,htrue⟩ :=
    (WordLinearDecisionCompletion.Proof.domainAwareElimination maximum _ hs.2.1 ν).mp
      ⟨hdomains,htrue⟩
  let μ := Function.update ν maximum n
  have hregion : Region (commonTail D floor p) maximum p.variables μ := by
    intro i hi
    exact (frame_eval (commonTail D floor p) maximum (names p) μ).mp htrue.1 i
      (List.mem_dedup.mpr hi)
  have hm := (actual_matrix D maximum p hD hp).2 μ
    (region_at_matrix_tail D floor maximum p μ hmaximum hregion)
  have hresidue : Formula.eval μ (residue p) := hm.2.2.mpr ⟨q,hq,htrue.2⟩
  have horiginal := paid_original_residue D floor p μ hp (fun i hi => (hregion i hi).1)
  exact ⟨μ,fun i hi => (floor_le_commonTail D floor p).trans (hregion i hi).1,
    horiginal.1,horiginal.2.2.mp hresidue⟩

theorem high_complete (D floor : Nat) (p : Formula) (hD : 3 ≤ D)
    (hp : Formula.allowed D p) (hne : names p ≠ [])
    (htrue : SatisfiableAt (commonTail D floor p) p) :
    ∃ b ∈ highChildren D (commonTail D floor p) p, SatisfiableAt b.1 b.2 := by
  rcases htrue with ⟨ν,hlarge,hdomains,htrue⟩
  obtain ⟨maximum,hmaximum,hmax⟩ := exists_maximum (names p) hne ν
  have hregion : Region (commonTail D floor p) maximum p.variables ν := by
    intro i hi
    exact ⟨hlarge i hi,hmax i (List.mem_dedup.mpr hi)⟩
  have hm := (actual_matrix D maximum p hD hp).2 ν
    (region_at_matrix_tail D floor maximum p ν hmaximum hregion)
  have hresidue := (paid_original_residue D floor p ν hp hlarge).2.2.mpr htrue
  obtain ⟨q,hq,hqtrue⟩ := hm.2.2.mp hresidue
  have hs := high_body_syntax D (commonTail D floor p) maximum p q hD hp hmaximum hq
  have hframe : Formula.eval ν (frame (commonTail D floor p) maximum (names p)) := by
    apply (frame_eval _ _ _ _).mpr
    intro i hi
    exact hregion i (List.mem_dedup.mp hi)
  have hbody : Formula.meaningful (.conj (frame (commonTail D floor p) maximum (names p)) q) ν :=
    OutcomeTransportProof.transport_meaningful_conj _ _ ν (frame_meaningful _ _ _ ν) (hm.2.1 q hq)
  have hu : Function.update ν maximum (ν maximum) = ν := by
    funext i
    by_cases hi : i = maximum
    · simp [hi]
    · simp [Function.update_of_ne hi]
  have helim := (WordLinearDecisionCompletion.Proof.domainAwareElimination maximum _ hs.2.1 ν).mpr
    ⟨ν maximum,by rw [hu]; exact ⟨hbody,hframe,hqtrue⟩⟩
  refine ⟨(commonTail D floor p,WordLinearDecisionCompletion.eliminate maximum
    (.conj (frame (commonTail D floor p) maximum (names p)) q)),?_,ν,?_,helim⟩
  · exact List.mem_flatMap.mpr ⟨maximum,hmaximum,List.mem_map.mpr ⟨q,hq,rfl⟩⟩
  · intro i hi
    have hh := (WordLinearDecisionCompletion.Proof.exactOutputVariables maximum _ hs.2.1 i).mp hi
    exact hlarge i (hs.2.2 i hh.2)

theorem actualChildEquivalence : BranchTargets.ActualChildEquivalence := by
  intro D floor p hD hp hne
  constructor
  · rintro ⟨ν,hfloor,hdomains,htrue⟩
    by_cases hsmall : ∃ x ∈ names p, ν x < commonTail D floor p
    · obtain ⟨b,hb,hbtrue⟩ := (prefix_equivalence floor (commonTail D floor p) p).mpr
        ⟨ν,hfloor,hdomains,htrue,hsmall⟩
      exact ⟨b,List.mem_append_left _ hb,hbtrue⟩
    · have hlarge : ∀ i ∈ p.variables, commonTail D floor p ≤ ν i := by
        intro i hi
        have hnot : ¬ν i < commonTail D floor p :=
          fun h => hsmall ⟨i,List.mem_dedup.mpr hi,h⟩
        omega
      obtain ⟨b,hb,hbtrue⟩ := high_complete D floor p hD hp hne ⟨ν,hlarge,hdomains,htrue⟩
      exact ⟨b,List.mem_append_right _ hb,hbtrue⟩
  · rintro ⟨b,hb,htrue⟩
    change b ∈ prefixChildren floor (commonTail D floor p) p ++
      highChildren D (commonTail D floor p) p at hb
    rcases List.mem_append.mp hb with hb | hb
    · obtain ⟨ν,hfloor,hdomains,hvalue,hsmall⟩ :=
        (prefix_equivalence floor (commonTail D floor p) p).mp ⟨b,hb,htrue⟩
      exact ⟨ν,hfloor,hdomains,hvalue⟩
    · exact high_child_sound D floor p hD hp b hb htrue

#print axioms actual_matrix
#print axioms high_body_syntax
#print axioms high_child_syntax
#print axioms actualChildSyntax
#print axioms region_at_matrix_tail
#print axioms paid_original_residue
#print axioms high_child_sound
#print axioms high_complete
#print axioms actualChildEquivalence

end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchProof
