import LogicLineages.PersistentMarking.NumberedWindowSimulationData
import LogicLineages.PersistentMarking.NumberedWindowPreservationSubstitutionProof

namespace LogicLineages.PersistentMarking.NumberedWindowExternalSubstitutionTargets
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary NumberedWindowSimulationData
open NumberedWindowPreservationBoundProof

/-- The literal beta instance of one typed lexical binder. -/
def bodyInstance {S K C σ τ} (hk : DecisionSourceUniverse.Closed K)
    (body : WindowCarrier S K (C.push σ) τ) (argument : WindowCarrier S K C σ) :
    WindowCarrier S K C τ :=
  ⟨substitute (.cons argument.val .nil) 0 body.val,
    NumberedWindowPreservationSubstitutionProof.term S K hk _ 0 _ _ _ _ body.property
      (one hk argument.property)⟩

/-- Apply the very same compatible literal substitution to both bodies. -/
def CompatibleBodySubstitutionPrimary : Prop :=
  ∀ S K values d C D τ q r, DecisionSourceUniverse.Closed K →
    Compatible S K values d C D → InWindow S K C τ q → Primary S K C τ q r →
    Primary S K D τ (substitute values d q) (substitute values d r)

/-- Literal one-binder substitution preserves equality of body classes
when the supplied argument carrier is held fixed. -/
def LiteralBodyClassSubstitution : Prop :=
  ∀ S K C σ τ (hk : DecisionSourceUniverse.Closed K)
    (q r : WindowCarrier S K (C.push σ) τ) (u : WindowCarrier S K C σ),
    (bodyInstance hk q u).val = substitute (.cons u.val .nil) 0 q.val ∧
    (classOf q = classOf r → classOf (bodyInstance hk q u) = classOf (bodyInstance hk r u))

end LogicLineages.PersistentMarking.NumberedWindowExternalSubstitutionTargets
