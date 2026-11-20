import LogicLineages.PersistentMarking.NumberedWindowExternalSubstitutionTargets

namespace LogicLineages.PersistentMarking.NumberedWindowExternalArgumentSubstitutionTargets
open NumberedWindowSyntax NumberedWindowPrimary NumberedWindowSimulationData
open NumberedWindowExternalSubstitutionTargets

/-- The same lexical shift of a typed Primary judgment preserves the
actual relation in an admitting target lexical context. -/
def LexicalShiftPreservesPrimary : Prop :=
  ∀ S K C D τ q r amount cutoff,
    Spine.ShiftCompatible amount cutoff C D → Primary S K C τ q r →
      Primary S K D τ (shift amount cutoff q) (shift amount cutoff r)

def LiteralArgumentClassSubstitution : Prop :=
  ∀ S K C σ τ (hk : DecisionSourceUniverse.Closed K)
    (body : WindowCarrier S K (C.push σ) τ) (a b : WindowCarrier S K C σ),
    classOf a = classOf b → classOf (bodyInstance hk body a) = classOf (bodyInstance hk body b)

/-- Literal beta endpoints agree for every representative pair of the
same original body class and argument class. -/
def LiteralInstanceClassSubstitution : Prop :=
  ∀ S K C σ τ (hk : DecisionSourceUniverse.Closed K)
    (body other : WindowCarrier S K (C.push σ) τ) (a b : WindowCarrier S K C σ),
    classOf body = classOf other → classOf a = classOf b →
      classOf (bodyInstance hk body a) = classOf (bodyInstance hk other b)

end LogicLineages.PersistentMarking.NumberedWindowExternalArgumentSubstitutionTargets
