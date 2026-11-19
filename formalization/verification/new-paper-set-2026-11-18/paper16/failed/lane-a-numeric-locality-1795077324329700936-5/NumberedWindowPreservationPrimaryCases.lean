import LogicLineages.PersistentMarking.NumberedWindowPreservationGuardProof

namespace LogicLineages.PersistentMarking.NumberedWindowPreservationPrimaryCases
open NumberedWindowSyntax NumberedWindowDomain
open NumberedWindowPreservationGuardProof
open NumberedWindowNumberedDomainProof (ArgsGuard)
open NumberedWindowApplicationDomainProof (rootInWindow)

theorem lamTransfer {S K C σ τ q r} (hk : DecisionSourceUniverse.Closed K)
    (hq : Typed (C.push σ) q τ) (hr : Typed (C.push σ) r τ)
    (hm : TermGuard S K q → TermGuard S K r)
    (hg : TermGuard S K (.lam σ q)) :
    TermGuard S K (.lam σ r) := by
  have hw : InWindow S K C (.arrow σ τ) (.lam σ q) := ⟨.lam hq,hg⟩
  have hr' : InWindow S K (C.push σ) τ r := ⟨hr,hm (lamBody hw).2⟩
  exact (NumberedWindowPreservationGuardProof.lam (hk _ (rootInWindow hw)) hr').2

theorem appFunctionTransfer {S K C σ τ q r a} (hk : DecisionSourceUniverse.Closed K)
    (hq : Typed C q (.arrow σ τ)) (ha : Typed C a σ)
    (hm : TermGuard S K q → TermGuard S K r)
    (hg : TermGuard S K (.auxApp σ τ q a)) :
    TermGuard S K (.auxApp σ τ r a) := by
  have hw : InWindow S K C τ (.auxApp σ τ q a) := ⟨.auxApp hq ha,hg⟩
  have parts := appParts hw
  exact appGuard hk (rootInWindow parts.1) (hm parts.1.2) parts.2.2

theorem appArgumentTransfer {S K C σ τ q a b} (hk : DecisionSourceUniverse.Closed K)
    (hq : Typed C q (.arrow σ τ)) (ha : Typed C a σ)
    (hm : TermGuard S K a → TermGuard S K b)
    (hg : TermGuard S K (.auxApp σ τ q a)) :
    TermGuard S K (.auxApp σ τ q b) := by
  have hw : InWindow S K C τ (.auxApp σ τ q a) := ⟨.auxApp hq ha,hg⟩
  have parts := appParts hw
  exact appGuard hk (rootInWindow parts.1) parts.1.2 (hm parts.2.2)

theorem ordinaryExchange {S K C f g bs cs}
    (hb : BaseTyped C bs f.arguments) (hg : HeadInWindow S K g)
    (hm : ArgsGuard S K bs → ArgsGuard S K cs)
    (h : TermGuard S K (.ordinary f bs)) :
    TermGuard S K (.ordinary g cs) := by
  have hw : InWindow S K C f.result (.ordinary f bs) := ⟨.ordinary hb,h⟩
  exact ordinaryGuard hg (hm (ordinaryParts hw).2.2)

theorem ordinaryCong {S K C f bs cs} (hb : BaseTyped C bs f.arguments)
    (hm : ArgsGuard S K bs → ArgsGuard S K cs)
    (h : TermGuard S K (.ordinary f bs)) :
    TermGuard S K (.ordinary f cs) := by
  have hw : InWindow S K C f.result (.ordinary f bs) := ⟨.ordinary hb,h⟩
  obtain ⟨_,hf,hbs⟩ := ordinaryParts hw
  exact ordinaryGuard hf (hm hbs)

theorem numberedExchange {S K C f g τ k bs cs es} (hk : DecisionSourceUniverse.Closed K)
    (hb : BaseTyped C bs f.arguments) (he : ExtrasTyped C es)
    (hg : HeadInWindow S K g) (hm : ArgsGuard S K bs → ArgsGuard S K cs)
    (h : TermGuard S K (.numbered f τ k bs es)) :
    TermGuard S K (.numbered g τ k cs es) := by
  have hw : InWindow S K C τ (.numbered f τ k bs es) := ⟨.numbered hb he,h⟩
  obtain ⟨_,_,_,hbs,hes⟩ := NumberedWindowNumberedDomainProof.parts hw
  exact numberedGuard hg (hk _ (rootInWindow hw)) (hm hbs) hes

theorem numberedBaseCong {S K C f τ k bs cs es} (hk : DecisionSourceUniverse.Closed K)
    (hb : BaseTyped C bs f.arguments) (he : ExtrasTyped C es)
    (hm : ArgsGuard S K bs → ArgsGuard S K cs)
    (h : TermGuard S K (.numbered f τ k bs es)) :
    TermGuard S K (.numbered f τ k cs es) := by
  have hw : InWindow S K C τ (.numbered f τ k bs es) := ⟨.numbered hb he,h⟩
  obtain ⟨_,_,hf,hbs,hes⟩ := NumberedWindowNumberedDomainProof.parts hw
  exact numberedGuard hf (hk _ (rootInWindow hw)) (hm hbs) hes

theorem numberedExtrasCong {S K C f τ k bs es ds} (hk : DecisionSourceUniverse.Closed K)
    (hb : BaseTyped C bs f.arguments) (he : ExtrasTyped C es)
    (hm : ArgsGuard S K es → ArgsGuard S K ds)
    (h : TermGuard S K (.numbered f τ k bs es)) :
    TermGuard S K (.numbered f τ k bs ds) := by
  have hw : InWindow S K C τ (.numbered f τ k bs es) := ⟨.numbered hb he,h⟩
  obtain ⟨_,_,hf,hbs,hes⟩ := NumberedWindowNumberedDomainProof.parts hw
  exact numberedGuard hf (hk _ (rootInWindow hw)) hbs (hm hes)

end LogicLineages.PersistentMarking.NumberedWindowPreservationPrimaryCases
