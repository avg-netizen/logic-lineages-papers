module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimaryExchangeHeadProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimaryExchangeShapeProof
open NumberedWindowSyntax NumberedWindowPrimaryExchange

theorem ordinaryShape {S K f g bs cs} :
    ExchangeShape S K (.ordinary f bs) (.ordinary g cs) ↔
      ((AllowedHeadPair S K f g ∧ f.result = g.result) ∧ bs.toList.Perm cs.toList) ∨
        (f = g ∧ ArgsExchangeShape S K bs cs) := by
  constructor
  · intro h
    cases h with
    | ordinary hp e hs => exact Or.inl ⟨⟨hp,e⟩,hs⟩
    | ordinaryBase hs => exact Or.inr ⟨rfl,hs⟩
  · rintro (⟨⟨hp,e⟩,hs⟩ | ⟨rfl,hs⟩)
    · exact .ordinary hp e hs
    · exact .ordinaryBase hs

theorem numberedShape {S K f g σ τ k j bs cs es ds} :
    ExchangeShape S K (.numbered f σ k bs es) (.numbered g τ j cs ds) ↔
      (σ = τ ∧ k = j) ∧
        (((AllowedHeadPair S K f g ∧ bs.toList.Perm cs.toList) ∧ es = ds) ∨
          (f = g ∧ ((ArgsExchangeShape S K bs cs ∧ es = ds) ∨
            (bs = cs ∧ ArgsExchangeShape S K es ds)))) := by
  constructor
  · intro h
    cases h with
    | numbered hp hs => exact ⟨⟨rfl,rfl⟩,Or.inl ⟨⟨hp,hs⟩,rfl⟩⟩
    | numberedBase hs => exact ⟨⟨rfl,rfl⟩,Or.inr ⟨rfl,Or.inl ⟨hs,rfl⟩⟩⟩
    | numberedExtra hs => exact ⟨⟨rfl,rfl⟩,Or.inr ⟨rfl,Or.inr ⟨rfl,hs⟩⟩⟩
  · rintro ⟨⟨rfl,rfl⟩,h⟩
    rcases h with ⟨⟨hp,hs⟩,rfl⟩ | ⟨rfl,h⟩
    · exact .numbered hp hs
    · rcases h with ⟨hs,rfl⟩ | ⟨rfl,hs⟩
      · exact .numberedBase hs
      · exact .numberedExtra hs

theorem lambdaShape {S K σ τ Q R} :
    ExchangeShape S K (.lam σ Q) (.lam τ R) ↔ σ = τ ∧ ExchangeShape S K Q R := by
  constructor
  · intro h
    cases h with
    | lam h => exact ⟨rfl,h⟩
  · rintro ⟨rfl,h⟩
    exact .lam h

theorem auxShape {S K σ τ ρ υ Q R A B} :
    ExchangeShape S K (.auxApp σ τ Q A) (.auxApp ρ υ R B) ↔
      (σ = ρ ∧ τ = υ) ∧ ((ExchangeShape S K Q R ∧ A = B) ∨
        (Q = R ∧ ExchangeShape S K A B)) := by
  constructor
  · intro h
    cases h with
    | applicationFunction h => exact ⟨⟨rfl,rfl⟩,Or.inl ⟨h,rfl⟩⟩
    | applicationArgument h => exact ⟨⟨rfl,rfl⟩,Or.inr ⟨rfl,h⟩⟩
  · rintro ⟨⟨rfl,rfl⟩,h⟩
    rcases h with ⟨h,rfl⟩ | ⟨rfl,h⟩
    · exact .applicationFunction h
    · exact .applicationArgument h

theorem consShape {S K Q R qs rs} :
    ArgsExchangeShape S K (.cons Q qs) (.cons R rs) ↔
      (ExchangeShape S K Q R ∧ qs = rs) ∨ (Q = R ∧ ArgsExchangeShape S K qs rs) := by
  constructor
  · intro h
    cases h with
    | first h => exact Or.inl ⟨h,rfl⟩
    | later h => exact Or.inr ⟨rfl,h⟩
  · rintro (⟨h,rfl⟩ | ⟨rfl,h⟩)
    · exact .first h
    · exact .later h

end LogicLineages.PersistentMarking.NumberedWindowPrimaryExchangeShapeProof
