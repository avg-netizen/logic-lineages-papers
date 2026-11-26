import LogicLineages.PersistentMarking.NumberedWindowOrdinaryQuoteProof

namespace LogicLineages.PersistentMarking.NumberedWindowOrdinaryDomainProof
open NumberedWindowSyntax NumberedWindowOrdinaryTranslation NumberedWindowTraceBudgetTargets

mutual
private theorem ordinary (q : Spine.Expr) (h : Spine.Ordinary q) : ∃ Q, tr q = some Q := by
  cases q with
  | free σ x => exact ⟨.free σ x,rfl⟩
  | bound σ i => exact ⟨.bound σ i,rfl⟩
  | lam σ q =>
    obtain ⟨out,e⟩ := ordinary q h
    exact ⟨.lam σ out,by simp only [tr,e,Option.map_some]⟩
  | head f bs =>
    obtain ⟨As,e⟩ := args bs h
    exact ⟨.ordinary f As,by simp only [tr,e,Option.map_some]⟩
  | marked f τ bs es => exact h.elim
termination_by sizeOf q

private theorem args (bs : Spine.Args) (h : Spine.OrdinaryArgs bs) : ∃ As, trArgs bs = some As := by
  cases bs with
  | nil => exact ⟨.nil,rfl⟩
  | cons q qs =>
    obtain ⟨out,hq⟩ := ordinary q h.1
    obtain ⟨rest,hs⟩ := args qs h.2
    exact ⟨.cons out rest,by simp [trArgs,hq,hs]⟩
termination_by sizeOf bs
end

theorem termDomain : OrdinaryTrDomain :=
  fun q => ⟨fun ⟨out,h⟩ => (NumberedWindowOrdinaryQuoteProof.term q out h).1,ordinary q⟩

theorem listDomain : OrdinaryTrArgsDomain :=
  fun bs => ⟨fun ⟨As,h⟩ => (NumberedWindowOrdinaryQuoteProof.list bs As h).1,args bs⟩

end LogicLineages.PersistentMarking.NumberedWindowOrdinaryDomainProof
