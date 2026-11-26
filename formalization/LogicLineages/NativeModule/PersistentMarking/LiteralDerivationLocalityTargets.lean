module

public import LogicLineages.NativeModule.PersistentMarking.LiteralDerivationTree
public import LogicLineages.NativeModule.PersistentMarking.DecisionSourceUniverse

@[expose] public section

namespace LogicLineages.PersistentMarking.LiteralDerivationLocalityTargets
open Spine LiteralDerivationTree DecisionInventory

/-- Literal declaration-retaining support of each actual root judgment.
Whole has a head and ordered argument lists, not an invented term or
an invented current output annotation. -/
def rootTypes : Judgment → List Ty
  | .weak q t | .strict q t => auxiliarySupport q ++ auxiliarySupport t
  | .matching xs ys | .multiset xs ys | .coverage xs ys => auxiliaryArgs xs ++ auxiliaryArgs ys
  | .whole f bs es ts => declaration f ++ auxiliaryArgs bs ++ auxiliaryArgs es ++ auxiliaryArgs ts

/-- Select has actual additional syntactic witnesses besides its child
judgment: the chosen argument, all original domain/arrow suffixes, and
the same owner's *entire* original typed tuple of copies. -/
def localTypes {S : Signature} {J : Judgment} (tree : Tree S J) : List Ty :=
  rootTypes J ++
    match tree with
    | .select f τ bs es _ _ q ds _ _ _ _ _ _ _ =>
      auxiliarySupport q ++ TypeSupport.subtypes (ArrowPrefix ds τ) ++
        auxiliaryArgs (ownerCopies f bs es ds)
    | _ => []

/-- Actual full certificate footprint, not the existence of some other
well-windowed derivation of the same Prop. `localTypes` pays the
ctor-local Select tuple even if a copy is absent from the result. -/
def footprint {S : Signature} {J : Judgment} (tree : Tree S J) : List Ty :=
  localTypes tree ++ match tree with
  | .var _ _ => []
  | .abs _ _ _ _ _ _ _ _ _ t => footprint t
  | .funHead _ _ _ _ _ _ _ _ t => footprint t
  | .put _ _ _ _ _ t => footprint t
  | .select _ _ _ _ _ _ _ _ _ _ _ _ _ _ t => footprint t
  | .fabs _ _ _ _ _ _ _ _ _ _ _ t => footprint t
  | .copy _ _ _ _ _ _ _ _ t => footprint t
  | .stat _ _ _ _ _ _ _ _ m w => footprint m ++ footprint w
  | .strictIntro _ _ _ _ _ _ _ t => footprint t
  | .matchingNil => []
  | .matchingCons _ _ _ _ _ _ t more => footprint t ++ footprint more
  | .multisetReplace _ _ _ _ _ _ _ _ _ m c => footprint m ++ footprint c
  | .coverageNil _ => []
  | .coverageCons _ _ _ _ _ _ t more => footprint t ++ footprint more
  | .wholeNil _ _ _ => []
  | .wholeCons _ _ _ _ _ t more => footprint t ++ footprint more

def CertificateExact : Prop := ∀ S J, Holds S J ↔ _root_.Nonempty (Tree S J)

def SymbolicLocality : Prop := ∀ (S : Signature) (K : List Ty) (J : Judgment) (tree : Tree S J),
  DecisionSourceUniverse.Closed K →
  (∀ ρ, ρ ∈ rootTypes J → ρ ∈ K) →
  ∀ ρ, ρ ∈ footprint tree → ρ ∈ K

end LogicLineages.PersistentMarking.LiteralDerivationLocalityTargets
