module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalDeletionCompleteTargets
public import LogicLineages.ModelsAlgebra.PGroups.TerminalDeletionOddProof
public import LogicLineages.ModelsAlgebra.PGroups.TerminalDeletionEvenProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem terminal_deletion_source_lemma : Targets.terminalDeletionSourceLemma := by
  intro G _ _ p _ hG rG γ K T N hsplit hdis hN hbound hw
  obtain ⟨hr,he,hred,hzero,hlen,hodd⟩ :=
    terminal_deletion_odd G p hG rG γ K T N hsplit hdis hN hbound hw
  exact ⟨hr,he,hred,hzero,hlen,hodd,
    terminal_deletion_even G p hG rG γ K T N hsplit hdis hN hbound hw⟩
end LogicLineages.ModelsAlgebra.PGroups
