import LogicLineages.PersistentMarking.NumberedWindowNeutralApplicationAddress
import LogicLineages.PersistentMarking.NumberedWindowOuterShapeTargets
import LogicLineages.PersistentMarking.NumberedWindowDirectClassAddressTargets
import LogicLineages.PersistentMarking.NumberedWindowAddressApplicationTargets

namespace LogicLineages.PersistentMarking.NumberedWindowNeutralApplicationAddressTargets
open Spine
open NumberedWindowNeutralApplicationAddress NumberedWindowOuterShape
open NumberedWindowDirectClassAddressTargets NumberedWindowAddressApplication
open NumberedWindowArithmeticScalarTargets

/-- A direct reduct of an actual non-lambda application is bottom, or
the same application at the function reduct extracted from the supplied edge. -/
def ExactNeutralApplicationAddress : Prop :=
  ∀ (S : Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∀ function argument applied target certificate tag,
      outerShape (fixed S K) function = some tag → tag ≠ 2 →
      graph (fixed S K) function argument applied = true →
      literalDirect S K applied certificate target = true →
      outerShape (fixed S K) target = some 3 ∨
        ∃ next childCertificate,
          functionWitness (fixed S K) function certificate = some (next,childCertificate) ∧
          literalDirect S K function childCertificate next = true ∧
          graph (fixed S K) next argument target = true

end LogicLineages.PersistentMarking.NumberedWindowNeutralApplicationAddressTargets
