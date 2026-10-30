module
public import LogicLineages.OrdinalComparison.ProfileReserveTargets
public import LogicLineages.OrdinalComparison.ProfileReserveWordProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem fullActualEffectiveProfileReserve : Targets.FullActualEffectiveProfileReserve := by
  intro ell hlarge he E hv
  dsimp only
  let word := profileBoundWord E
  let R := profileReserveBlocks word
  have hc := actualProfileBoundCompiler (Ordinal.omega0 ^ ell) hlarge E hv
  have hw : ∀ rho ∈ word, Order.IsSuccLimit rho.1.repr := fun rho hr => (hc.2.1 rho hr).1
  have hbudget := actualProfileReserveBudgetCalibration word hw
  refine ⟨hc.1, hc.2.1, hbudget.1, hbudget.2, ?_⟩
  intro z hz
  have hdom := (hc.2.2 z hz).1
  refine ⟨hdom, ?_⟩
  intro beta hb hpi hlead n hzn
  let initial := Ordinal.omega0 ^ beta * ((R : Nat) : Ordinal) + (n : Ordinal)
  have hword := actualProfileReserveWordConsumer beta hb hpi word
    (fun rho hr => ⟨hw rho hr, hlead rho hr⟩) n
  have hmono := (actualValidProfileWordStrictMono word hw).monotone hzn
  have hterm : actualFixedLimitProfileEval E z < actualTerminalValue initial :=
    hdom.trans_le (hmono.trans hword.1)
  have hq := reserveStagePrincipalMultipleFacts beta hpi R
  have hi := (actualFiniteTailClosureNorm (Ordinal.omega0 ^ beta * (R : Ordinal)) hq.1 n).1
  refine ⟨hterm, ?_⟩
  intro c
  have hm := actualCompensatedExitDominatesTerminal initial hi c
  exact hterm.trans_le (hm.trans (Nat.le_add_left _ c))

end LogicLineages.OrdinalComparison
