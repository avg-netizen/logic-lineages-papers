module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPositiveSimulationTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationQuotientProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowClosing NumberedWindowPreservationTargets
open NumberedWindowSimulationData NumberedWindowPositiveSimulationTargets

private theorem walk {S K C τ Q T} (path : TypedTrace S K C τ Q T) :
    AdmittedTrace path → ∃ hQ : InWindow S K C τ Q, ∃ hT : InWindow S K C τ T,
      (rawLength path = 0 → classOf ⟨Q,hQ⟩ = classOf ⟨T,hT⟩) ∧
      (0 < rawLength path → RS S K C τ (classOf ⟨Q,hQ⟩) (classOf ⟨T,hT⟩)) := by
  induction path with
  | done ht =>
    intro h
    have hw := h _ List.mem_cons_self
    exact ⟨hw,hw,fun _ => rfl,fun h => False.elim (Nat.not_lt_zero _ h)⟩
  | raw hq hr hStep tail ih =>
    intro h
    have hwQ := h _ List.mem_cons_self
    obtain ⟨hwR,hwT,heq,hpos⟩ := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
    let Qc : WindowCarrier S K C τ := ⟨_,hwQ⟩
    let Rc : WindowCarrier S K C τ := ⟨_,hwR⟩
    let Tc : WindowCarrier S K C τ := ⟨_,hwT⟩
    have e : ClassEdge (classOf Qc) (classOf Rc) := ⟨Qc,Rc,rfl,rfl,hStep⟩
    refine ⟨hwQ,hwT,?_,?_⟩
    · intro hz
      change rawLength tail + 1 = 0 at hz
      omega
    · intro _
      change RS S K C τ (classOf Qc) (classOf Tc)
      cases hl : rawLength tail with
      | zero =>
        have hSame : classOf Rc = classOf Tc := heq hl
        rw [← hSame]
        exact .one e
      | succ n =>
        have hl' : 0 < rawLength tail := by rw [hl]; exact Nat.zero_lt_succ _
        exact .more e (hpos hl')
  | equiv hPrim tail ih =>
    intro h
    have hwQ := h _ List.mem_cons_self
    obtain ⟨hwR,hwT,heq,hpos⟩ := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
    let Qc : WindowCarrier S K C τ := ⟨_,hwQ⟩
    let Rc : WindowCarrier S K C τ := ⟨_,hwR⟩
    let Tc : WindowCarrier S K C τ := ⟨_,hwT⟩
    have e : classOf Qc = classOf Rc := Quot.sound hPrim
    refine ⟨hwQ,hwT,?_,?_⟩
    · intro hz
      exact e.trans (heq hz)
    · intro hp
      change RS S K C τ (classOf Qc) (classOf Tc)
      rw [e]
      exact hpos hp

theorem positive : PositiveTraceToClassPath := by
  intro S K C τ Q T path ha hp
  obtain ⟨hq,ht,_h0,hn⟩ := walk path ha
  exact ⟨hq,ht,hn hp⟩

end LogicLineages.PersistentMarking.NumberedWindowSimulationQuotientProof
