module
public import LogicLineages.PermittedControl.OriginalPrintedGreatestGateResolutionTargets
import LogicLineages.PermittedControl.OriginalPrintedGreatestGateResolutionSupportProof
import LogicLineages.PermittedControl.OriginalGreatestGateGrowthOrdinaryProof
import LogicLineages.PermittedControl.OriginalGreatestGateGrowthCountProof
import LogicLineages.PermittedControl.FixedHeadCollapseGraphSemanticProof
import LogicLineages.PermittedControl.OriginalNaturalFieldGatesProof
import LogicLineages.PermittedControl.PreparedParameterActualProof
import LogicLineages.PermittedControl.ActualShortCountCleanupCountProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedGreatestGateResolution
open OrdinalComparison FieldComparison PreparedProjection
open OriginalNaturalFieldGates (exactOrdinarySharedGateGraph)
open OriginalPrintedCircuitNormalization (NormalizedGate)
open OriginalPrintedPlainMatrixInfiniteLow (circuit matrix)
open OriginalPrintedPlainMatrixLinearProjection (top replay safeMinimum)
open OriginalMatrixDenseRanks (support)
open OriginalNormalizedCircuitMatrix (LimitHead)
open ActualFiniteOrderBranches (rename)
open OriginalGreatestGateGrowth (longCountBound exactOrdinaryStrictGrowth exactLimitCollapseStrictGrowth
  exactLongCountStrictGrowth exactShortCountGraph)

theorem exactUniformGateResolution : ExactUniformGateResolution := by
  intro f B hf θ known gates p branch member ordered z paid g listed
  let ν := replay θ known gates p branch z
  let tag := rename branch
  let topRank := top branch
  have rawPay : safeMinimum B θ known gates p branch ≤ z := (le_max_left _ _).trans paid
  have localPay : gateBound g ≤ z :=
    (boundAt (circuit known gates p) g listed).trans ((le_max_right _ _).trans paid)
  have compare (s o : Nat) (hs : s ∈ support (matrix known gates p))
      (ho : o ∈ support (matrix known gates p)) (h : tag s = topRank) :
      ν o ≤ ν s ∧ ν s = z :=
    maximalInput B θ known gates p branch member ordered z rawPay s o hs ho h
  have graphReads (field : OriginalNaturalFieldGates.Gate) (live : field.graph f ν) :
      field.read f ν = some (some (ν field.output)) :=
    (exactOrdinarySharedGateGraph f field ν ν).1.mpr live
  cases g with
  | base base =>
      cases base with
      | affine e o => rfl
      | limitPair head e s o =>
          by_cases atTop : tag s = topRank
          · change AffineCollapseGraphComposition.graph f head e s o ν ↔
              (if tag s = topRank then Mode.impossible else .keep (.base (.limitPair head e s o))).Holds f ν
            rw [if_pos atTop]
            constructor
            · intro live
              have h := ((FixedHeadCollapseGraph.sourceGraph f B hf (head,ν s)).1 (ν o)).mp live.2
              have typed : LimitHead head := ⟨h.1.1,h.1.2.1⟩
              obtain ⟨hs,ho⟩ := limitSupport known gates p head e s o typed listed
              exact (not_lt_of_ge (compare s o hs ho atTop).1)
                (exactLimitCollapseStrictGrowth f B hf head (ν s) (ν o) live.2)
            · intro impossible
              exact False.elim impossible
          · change _ ↔ (if tag s = topRank then Mode.impossible else
                .keep (.base (.limitPair head e s o))).Holds f ν
            rw [if_neg atTop] <;> rfl
  | field field =>
      have orig := fieldSupport known gates p field listed
      cases field with
      | iterate k s o =>
          cases k with
          | zero => rfl
          | succ k =>
              by_cases atTop : tag s = topRank
              · change (OriginalNaturalFieldGates.Gate.iterate (k+1) s o).graph f ν ↔
                  (if tag s = topRank then Mode.impossible else .keep (.field (.iterate (k+1) s o))).Holds f ν
                rw [if_pos atTop]
                constructor
                · intro graph
                  have actual : LowerOperandActual f ν (.ordinary s (.iterate (k+1))) (ν o) :=
                    (preparedTiedProjection.1 f ν (.ordinary s (.iterate (k+1))) (ν o)).mp (graphReads _ graph)
                  exact (not_lt_of_ge (compare s o orig.1 orig.2 atTop).1)
                    (exactOrdinaryStrictGrowth f B hf ν s (.iterate (k+1)) (ν o) (Nat.succ_pos k) actual)
                · intro impossible
                  exact False.elim impossible
              · change _ ↔ (if tag s = topRank then Mode.impossible else
                    .keep (.field (.iterate (k+1) s o))).Holds f ν
                rw [if_neg atTop] <;> rfl
      | entry interval s o =>
          cases interval with
          | identity mu => rfl
          | proper lam mu =>
              by_cases atTop : tag s = topRank
              · change (OriginalNaturalFieldGates.Gate.entry (.proper lam mu) s o).graph f ν ↔
                  (if tag s = topRank then Mode.impossible else .keep (.field (.entry (.proper lam mu) s o))).Holds f ν
                rw [if_pos atTop]
                constructor
                · intro graph
                  have actual : LowerOperandActual f ν (.ordinary s (.entry 0 lam mu)) (ν o) :=
                    (preparedTiedProjection.1 f ν (.ordinary s (.entry 0 lam mu)) (ν o)).mp (graphReads _ graph)
                  exact (not_lt_of_ge (compare s o orig.1 orig.2 atTop).1)
                    (exactOrdinaryStrictGrowth f B hf ν s (.entry 0 lam mu) (ν o) True.intro actual)
                · intro impossible
                  exact False.elim impossible
              · change _ ↔ (if tag s = topRank then Mode.impossible else
                    .keep (.field (.entry (.proper lam mu) s o))).Holds f ν
                rw [if_neg atTop] <;> rfl
      | count interval s o =>
          cases interval with
          | identity mu => rfl
          | proper lam mu =>
              change (OriginalNaturalFieldGates.Gate.count (.proper lam mu) s o).graph f ν ↔
                (if tag s = topRank then
                  if 0 < shortGapLength lam mu then Mode.shortCount lam mu s o else .impossible
                else .keep (.field (.count (.proper lam mu) s o))).Holds f ν
              by_cases atTop : tag s = topRank
              · rw [if_pos atTop]
                by_cases short : 0 < shortGapLength lam mu
                · rw [if_pos short]
                  exact exactShortCountGraph f B hf ν lam mu s o short
                · rw [if_neg short]
                  constructor
                  · intro graph
                    have zero : shortGapLength lam mu = 0 := by omega
                    have actual : LowerOperandActual f ν (.count s lam mu) (ν o) :=
                      (preparedTiedProjection.1 f ν (.count s lam mu) (ν o)).mp (graphReads _ graph)
                    have long : LongField (.entry 0 lam mu) :=
                      ActualShortCountCleanup.longOfRetained f ν (.count s lam mu) (ν o) actual zero
                    have cmp := compare s o orig.1 orig.2 atTop
                    have bound : longCountBound lam mu ≤ ν s := by
                      change (if shortGapLength lam mu = 0 then longCountBound lam mu else 0) ≤ z at localPay
                      rw [if_pos zero] at localPay
                      rwa [cmp.2]
                    have impossible := exactLongCountStrictGrowth f B hf ν s lam mu (ν o) (ν o)
                      long bound cmp.1 actual
                    omega
                  · intro impossible
                    exact False.elim impossible
              · rw [if_neg atTop] <;> rfl

theorem exactUniformOriginalResolvedBranch : ExactUniformOriginalResolvedBranch := by
  intro f B hf θ known gates p branch member checked z paid prior positive
  let ν := replay θ known gates p branch z
  have exactPlan (g : NormalizedGate) (hg : g ∈ circuit known gates p) :=
    exactUniformGateResolution f B hf θ known gates p branch member checked z paid g hg
  constructor
  · rintro ⟨pr,graph,terminal⟩
    refine ⟨pr,?_,terminal⟩
    intro m hm
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hm
    exact (exactPlan g hg).mp (graph g hg)
  · rintro ⟨pr,graph,terminal⟩
    refine ⟨pr,?_,terminal⟩
    intro g hg
    exact (exactPlan g hg).mpr (graph _ (List.mem_map.mpr ⟨g,hg,rfl⟩))

end LogicLineages.PermittedControl.OriginalPrintedGreatestGateResolution
