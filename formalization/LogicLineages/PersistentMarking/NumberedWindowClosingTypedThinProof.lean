import LogicLineages.PersistentMarking.NumberedWindowClosingTypedThinCore
import LogicLineages.PersistentMarking.NumberedWindowClosingInventoryProof

namespace LogicLineages.PersistentMarking.NumberedWindowClosingTypedThinProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowClosing

theorem admissible {S K n d C D τ q} (hc : CloseCompatible n d C D)
    (h : InWindow S K C τ q) : InWindow S K D τ (closeAt n d q) := by
  obtain ⟨_,hs,hh⟩ := NumberedWindowClosingInventoryProof.term n d q
  exact ⟨NumberedWindowClosingTypedThinCore.term n d C D q τ h.1 hc,
    fun t hp => h.2.1 t (hs ▸ hp),fun f hf => h.2.2 f (hh ▸ hf)⟩

end LogicLineages.PersistentMarking.NumberedWindowClosingTypedThinProof
