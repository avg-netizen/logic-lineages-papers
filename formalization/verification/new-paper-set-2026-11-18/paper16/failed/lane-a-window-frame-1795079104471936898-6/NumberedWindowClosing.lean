import LogicLineages.PersistentMarking.NumberedWindowPreservationTargets

namespace LogicLineages.PersistentMarking.NumberedWindowClosing
open NumberedWindowSyntax NumberedWindowPreservationTargets
open NameBridge (Name)

/- Numeric analogue of the original typed free-name closing map.
An already-bound position stays put. C/D compatibility below is therefore
an extension retaining the existing positions, not a shifted insertion
into an arbitrary occupied binder context. -/
mutual
def closeAt (name : Name) (depth : Nat) : NTerm → NTerm
  | .free σ x => if (σ,x) = name then .bound σ depth else .free σ x
  | .bound σ i => .bound σ i
  | .lam σ q => .lam σ (closeAt name (depth+1) q)
  | .bottom σ => .bottom σ
  | .ordinary f bs => .ordinary f (closeArgsAt name depth bs)
  | .numbered f τ k bs es => .numbered f τ k (closeArgsAt name depth bs) (closeArgsAt name depth es)
  | .auxApp σ τ q a => .auxApp σ τ (closeAt name depth q) (closeAt name depth a)
def closeArgsAt (name : Name) (depth : Nat) : NArgs → NArgs
  | .nil => .nil
  | .cons q qs => .cons (closeAt name depth q) (closeArgsAt name depth qs)
end

def CloseCompatible (name : Name) (depth : Nat) (C D : Spine.BoundContext) : Prop :=
  D depth = some name.1 ∧ ∀ i τ, C i = some τ → D i = some τ

/-- Count genuine raw edges of the actual mixed trace. An equivalence
edge cannot contribute to the strict simulation's positivity. -/
def rawLength {S K C τ} {q t : NTerm} : TypedTrace S K C τ q t → Nat
  | .done _ => 0
  | .raw _ _ _ tail => rawLength tail + 1
  | .equiv _ tail => rawLength tail

end LogicLineages.PersistentMarking.NumberedWindowClosing
