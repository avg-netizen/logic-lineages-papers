import LogicLineages.PersistentMarking.NumberedWindowExternalTypeFactsTargets
import LogicLineages.PersistentMarking.NumberedWindowExternalNeutralChecks

namespace LogicLineages.PersistentMarking.NumberedWindowExternalAtomicClassesProof
open Spine NumberedWindowSyntax NumberedWindowPrimary NumberedWindowSimulationData
open NumberedWindowRules NumberedWindowExternalNeutralTargets NumberedWindowExternalTypeFactsTargets

private def leafView : NTerm → Option NTerm
  | .free σ i => some (.free σ i)
  | .bound σ i => some (.bound σ i)
  | .bottom σ => some (.bottom σ)
  | _ => none

private theorem leafPrimary {S K C τ q r} (h : Primary S K C τ q r) : leafView q = leafView r := by
  induction h using Primary.rec (motive_2 := fun _ _ _ _ _ => True) with
  | symm _ e => exact e.symm
  | trans _ _ e d => exact e.trans d
  | _ => first | rfl | trivial

private def classView {S K C τ} : Class S K C τ → Option NTerm :=
  Quot.lift (fun q : WindowCarrier S K C τ => leafView q.val) (fun _ _ h => leafPrimary h)

private theorem fromView {q v : NTerm} (h : leafView q = some v) : q = v := by
  cases q <;> simp_all [leafView]

private theorem sameLeaf {S K C τ} {q r : WindowCarrier S K C τ} {v : NTerm}
    (e : classOf q = classOf r) (h : leafView q.val = some v) : r.val = v := by
  have eq : leafView q.val = leafView r.val := congrArg classView e
  exact fromView (eq.symm.trans h)

private theorem bottomNo {S K τ r} (step : RawStep S K (.bottom τ) r) : False := by
  cases step with
  | bottom ne => exact ne rfl

private theorem freeOut {S K τ i r} (step : RawStep S K (.free τ i) r) : r = .bottom τ := by
  cases step
  rfl

private theorem boundOut {S K τ i r} (step : RawStep S K (.bound τ i) r) : r = .bottom τ := by
  cases step
  rfl

theorem bottomNeutral {S K C τ} {x : Class S K C τ} (hx : ClassBottom x) : ClassNonLambda x := by
  obtain ⟨q,hq,rfl⟩ := hx
  apply (NumberedWindowExternalNeutralChecks.exact_ExactNonLambdaRepresentatives S K C τ q).mpr
  rw [hq]
  intro σ body e
  cases e

theorem bottomNoEdge {S K C τ} {x y : Class S K C τ} (hx : ClassBottom x) (step : ClassEdge x y) :
    False := by
  obtain ⟨q,hq,rfl⟩ := hx
  obtain ⟨a,b,ha,_,raw⟩ := step
  have eq : a.val = .bottom τ := sameLeaf ha.symm (by rw [hq]; rfl)
  rw [eq] at raw
  exact bottomNo raw

theorem variableNeutral {S K C τ} {x : Class S K C τ} (hx : VariableClass x) : ClassNonLambda x := by
  obtain ⟨q,⟨i,hi⟩,rfl⟩ := hx
  apply (NumberedWindowExternalNeutralChecks.exact_ExactNonLambdaRepresentatives S K C τ q).mpr
  rcases hi with h | h <;> rw [h] <;> intro σ body e <;> cases e

theorem variableEdge {S K C τ} {x y : Class S K C τ} (hx : VariableClass x) (step : ClassEdge x y) :
    ClassBottom y := by
  obtain ⟨q,⟨i,hi⟩,rfl⟩ := hx
  obtain ⟨a,b,ha,hb,raw⟩ := step
  refine ⟨b,?_,hb⟩
  rcases hi with h | h
  · have eq : a.val = .free τ i := sameLeaf ha.symm (by rw [h]; rfl)
    rw [eq] at raw
    exact freeOut raw
  · have eq : a.val = .bound τ i := sameLeaf ha.symm (by rw [h]; rfl)
    rw [eq] at raw
    exact boundOut raw

end LogicLineages.PersistentMarking.NumberedWindowExternalAtomicClassesProof
