module
public import LogicLineages.ControlSensitivityCurrent.CurrentSelectedCarriersDefinitions
public import LogicLineages.ControlSensitivityCurrent.CurrentAffineHeadsDefinitions
public import LogicLineages.OrdinalComparison.SelectedAccountPreparationDefinitions
public import LogicLineages.OrdinalComparison.GroundCarrierTransportDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentReserve

open LogicLineages.OrdinalComparison (ordinalNaturalSum)
open LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open CurrentUnaryChain (commonUnits)
open ActiveScalarAnnotation SourceFreeOccurrences

/-- A carrier is the exact actual chosen-policy whole source vector, with its
actual scalar intact. The ground-free proof asserts literal source closure,
not an ordinal of the right value selected from outside the source domain. -/
structure Carrier (p : AdmissibleSum.Policy) where
  context : List Ty
  term : OriginalTerm context (Ty.curriedGround 1)
  vector : OrdinalVector context 1
  actual : AdmissibleAssignment.assignment p term = some vector
  noGround : ∀ x : Variable context .ground,
    (⟨.ground,x⟩ : PackedVariable context) ∉ freeOccurrences term

noncomputable def unitValue (f : Nat → Nat) {Γ : List Ty} (q : OrdinalExpression Γ) : Ordinal :=
  ParametricSourceSuccessor.denoteWith f (commonUnits (fun _ => 0)) q

noncomputable def Carrier.head {p : AdmissibleSum.Policy} (f : Nat → Nat) (a : Carrier p) : Ordinal :=
  unitValue f (a.vector 1)

/-- Ordered list of carrier occurrences; repeated uses of the same actual
source remain present. Natural ordinal addition realizes the finite multiset. -/
noncomputable def carrierSum {p : AdmissibleSum.Policy} (f : Nat → Nat) : List (Carrier p) → Ordinal
  | [] => 0
  | a :: as => ordinalNaturalSum (a.head f) (carrierSum f as)

/-- The finite accounting subtraction is Int, not truncated Nat subtraction.
A nonfinite local step may contribute delta-3 < 0. -/
def reserve {p : AdmissibleSum.Policy} (as : List (Carrier p)) (c : Nat) : Int :=
  (c : Int) - 3 * (as.length : Int)

/-- Exact actual carrier selected from an actual same-policy original
operator via fresh same-type name, literal zero saturation and closure. -/
def carrierFrom {p : AdmissibleSum.Policy} {f : Nat → Nat} {Γ : List Ty} {σ : Ty}
    {F : Variable Γ σ} {r : Nat} {t : OriginalTerm Γ (Ty.curriedGround (r+1))}
    {u : OrdinalVector Γ (Ty.curriedGround (r+1)).level}
    {w v : OrdinalVector (σ :: Γ) 1}
    (h : CurrentSelectedCarriers.Realization p f F r t u w v) : Carrier p :=
  ⟨σ :: Γ,CurrentSelectedCarriers.carrierAt F r t,v,h.2.2.1,h.2.2.2.2.2.1⟩

def LiteralOrigin (p : AdmissibleSum.Policy) (f : Nat → Nat) {k : Nat} {Γ : List Ty}
    (h : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)) (a : Carrier p) : Prop :=
  ∃ (r : Nat) (t : OriginalTerm (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (r+1)))
    (u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (r+1)).level)
    (w v : OrdinalVector (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ) 1),
    u (UnaryCarrier.headIndex r) = h ∧
    ∃ hA : CurrentSelectedCarriers.Realization p f
      (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) r t u w v, a = carrierFrom hA

/-- Literal ordered accounting, with distinct free/active constructors.
Row counts use the retained actual expression tree. When forming a fresh
account, each nonfinite constructor also certifies its literal actual
operator/carrier origin. Transport keeps the original ground-closed label
rather than inventing a new equal-valued label in its new typed context. -/
inductive AccountWith (p : AdmissibleSum.Policy) (f : Nat → Nat) (origins : Bool)
    {k : Nat} {Γ : List Ty} :
    OrdinalExpression (Ty.curriedGround (k+1) :: Γ) → List (Carrier p) → Nat → Prop where
  | free {q} (inactive : ¬ Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q) :
      AccountWith p f origins q [] 1
  | tracked : AccountWith p f origins (.var ⟨_,.here,0⟩) [] 1
  | add {a b xs ys c d}
      (active : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (.add a b))
      (left : AccountWith p f origins a xs c) (right : AccountWith p f origins b ys d) :
      AccountWith p f origins (.add a b) (xs ++ ys) (c+d+1)
  | finite {h t xs c} {n : Nat}
      (active : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (.collapse h t))
      (finite : unitValue f h = (n : Ordinal)) (tail : AccountWith p f origins t xs c) :
      AccountWith p f origins (.collapse h t) xs (c+n+HeadFiniteSurplus.surplus h)
  | nonfinite {h t xs c} (a : Carrier p)
      (active : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (.collapse h t))
      (nonfinite : Ordinal.omega0 ≤ unitValue f h)
      (exactHead : a.head f = unitValue f h)
      (origin : origins = true → LiteralOrigin p f h a)
      (tail : AccountWith p f origins t xs c) :
      AccountWith p f origins (.collapse h t) (xs ++ [a]) (c+HeadFiniteSurplus.surplus h)

abbrev Account (p : AdmissibleSum.Policy) (f : Nat → Nat) {k : Nat} {Γ : List Ty} :=
  @AccountWith p f false k Γ

abbrev SpawnedAccount (p : AdmissibleSum.Policy) (f : Nat → Nat) {k : Nat} {Γ : List Ty} :=
  @AccountWith p f true k Γ

/-- Dependent position changes move only the selected actual F. The ground
binder to be partially discharged is the literal new head z, possibly above
an arbitrary prefix of old names before the original selected F slot. -/
def before (k : Nat) (left right : List Ty)
    (q : OrdinalExpression ((.ground :: left) ++ Ty.curriedGround (k+1) :: right)) :
    OrdinalExpression (Ty.curriedGround (k+1) :: ((.ground :: left) ++ right)) :=
  SelectedAccountPreparation.prepare (.ground :: left) right (Ty.curriedGround (k+1)) q

def after (k : Nat) (left right : List Ty)
    (q : OrdinalExpression (left ++ Ty.curriedGround (k+1) :: right)) :
    OrdinalExpression (Ty.curriedGround (k+1) :: (left ++ right)) :=
  SelectedAccountPreparation.prepare left right (Ty.curriedGround (k+1)) q

/-- The stronger ground-lambda floor five is proved, not imposed on
annotation or on the arbitrary scalar accounting relation. -/
def sourceFloor {k Γ F n} (e : TrackedSource.Expr k Γ F n) : Int :=
  if TrackedSource.active e then
    match e with
    | .tracked => 1
    | .lam _ => 5
    | _ => 4
  else 1

end LogicLineages.ControlSensitivityCurrent.CurrentReserve
