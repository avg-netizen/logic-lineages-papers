module
public import LogicLineages.CartierObserverCurrent.HigherPolesGeometryTargets
public import LogicLineages.CartierObserverCurrent.FullTransientProof
public import LogicLineages.CartierObserverCurrent.HigherPolesWordProof
public meta import LogicLineages.Audit
@[expose] public section
universe u v
namespace LogicLineages.CartierObserverCurrent.HigherPolesGeometry
theorem geometricRemoval : Targets.GeometricRemoval.{u,v} := by
  intro K L _ _ _ _ _ _ σ d hd P hP
  let a := SourceBudget.transient d
  have transient (j : Nat) :=
    FullTransient.binaryTransient.2.2.2 K L σ d hd P hP (List.replicate j true)
  constructor
  · intro j
    simpa only [HigherPolesWord.repeatedWord] using (transient j).1
  · intro j z
    have hlen : SourceBudget.transient d ≤ (List.replicate (a + j) true).length := by
      simp only [List.length_replicate]
      exact Nat.le_add_right a j
    simpa only [HigherPolesWord.repeatedWord] using (transient (a + j)).2.2 hlen z

#audit_namespace LogicLineages.CartierObserverCurrent.HigherPolesGeometry
end LogicLineages.CartierObserverCurrent.HigherPolesGeometry
