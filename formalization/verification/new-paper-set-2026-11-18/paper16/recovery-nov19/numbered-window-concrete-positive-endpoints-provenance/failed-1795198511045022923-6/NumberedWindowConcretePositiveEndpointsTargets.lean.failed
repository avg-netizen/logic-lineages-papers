module
public import LogicLineages.PersistentMarking.NumberedWindowConcreteCheckers

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowConcretePositiveEndpointsTargets
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowScalarAlgorithm (Settings admitted least scalar)
open NumberedWindowConcreteCheckers (step positive)
open NumberedWindowPositivePathAlgorithm (advance hopView)

/-- The same supplied hop, including its actual raw witness, callback,
both least tests, and the callback's two original admission tests. -/
def HopReport (entries : Entries) (s : Settings) (ctx : List Nat)
    (ty source code target : Nat) : Prop :=
  ∃ q w r : Nat,
    hopView code = some (target,q,w,r) ∧
    step entries s ctx ty q w r = true ∧
    admitted s ctx ty q = true ∧ admitted s ctx ty r = true ∧
    least s ctx ty q = some source ∧ least s ctx ty r = some target

def ExactConcretePositiveHopReport : Prop :=
  ∀ (entries : Entries) (s : Settings) (ctx : List Nat) (ty source code target : Nat),
    advance (step entries s ctx ty) (least s ctx ty) (some source) code = some target →
    HopReport entries s ctx ty source code target

/-- No new certificate is chosen. The first and last hops are both in
the actual decoded list, and the input to the last is the result of
the original fold on precisely the prefix before it. A singleton has
the same head and last. All raw certificate codes are in scope. -/
def ExactConcretePositiveBoundaryHops : Prop :=
  ∀ (entries : Entries) (s : Settings) (ctx : List Nat) (ty source witness target : Nat),
    NumberedWindowPositivePathAlgorithm.positive (step entries s) (least s)
      ctx ty source witness target = true →
    ∃ (codes : List Nat) (first : Nat) (rest beforeLast : List Nat) (last firstOut lastIn : Nat),
      unpack witness = some codes ∧ codes = first :: rest ∧ codes = beforeLast ++ [last] ∧
      advance (step entries s ctx ty) (least s ctx ty) (some source) first = some firstOut ∧
      beforeLast.foldl (advance (step entries s ctx ty) (least s ctx ty)) (some source) =
        some lastIn ∧
      advance (step entries s ctx ty) (least s ctx ty) (some lastIn) last = some target ∧
      HopReport entries s ctx ty source first firstOut ∧
      HopReport entries s ctx ty lastIn last target

/-- Both visible original least results admit and are their own least
in the original pools recomputed at those results. No supplied seed
admission, same-pool, symmetry, or special settings hypothesis. -/
def ExactConcretePositiveRawEndpoints : Prop :=
  ∀ (entries : Entries) (s : Settings) (ctx : List Nat) (ty source witness target : Nat),
    NumberedWindowPositivePathAlgorithm.positive (step entries s) (least s)
      ctx ty source witness target = true →
    admitted s ctx ty source = true ∧ least s ctx ty source = some source ∧
    admitted s ctx ty target = true ∧ least s ctx ty target = some target

/-- On the original packed address numbers, successful actual positive
checking implies both actual original scalar bits. No arbitrary
application closure nor object derivation is asserted. -/
def ExactConcretePositiveScalarEndpoints : Prop :=
  ∀ (entries : Entries) (s : Settings) (x witness y : Nat),
    positive entries s x witness y = true →
    scalar s x = true ∧ scalar s y = true

end LogicLineages.PersistentMarking.NumberedWindowConcretePositiveEndpointsTargets
