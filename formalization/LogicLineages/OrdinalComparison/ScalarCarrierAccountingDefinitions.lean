module
public import LogicLineages.OrdinalComparison.SelectedAffineHeadDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ScalarCarrierAccounting
open ActiveScalarAnnotation SourceFreeOccurrences
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- Every label is an actual unary original source with its entire actual
canonical vector, including scalar, and a proved absence of free ground names.
Its own finite typed context is retained so a later ground-binder transport can
retain the same actual closed label rather than replacing it by an ordinal. -/
structure Carrier where
  context : List Ty
  term : OriginalTerm context (Ty.curriedGround 1)
  vector : OrdinalVector context 1
  assigned : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy term = some vector
  noGround : ∀ x : Variable context .ground,
    (⟨Ty.ground,x⟩ : PackedVariable context) ∉ freeOccurrences term

noncomputable def unitValue {Γ : List Ty} (e : OrdinalExpression Γ) : Ordinal :=
  denote (fun _ => 1) e

noncomputable def Carrier.head (c : Carrier) : Ordinal := unitValue (c.vector 1)

/-- Ordered occurrence list: equal labels at distinct nonfinite collapse
occurrences are retained, never collected or deduplicated. -/
noncomputable def carrierSum : List Carrier → Ordinal
  | [] => 0
  | c :: cs => ordinalNaturalSum c.head (carrierSum cs)

def reserve (cs : List Carrier) (c : Nat) : Int := (c : Int) - 3 * (cs.length : Int)

/-- Literal source accounting clauses. Whole F-free pieces are one stop;
active sums concatenate occurrence lists; finite heads retain the tail list;
nonfinite heads append exactly one genuine carrier with that exact unit field.
No transport or lower-reserve bound is postulated in this relation. -/
inductive Account {k : Nat} {Γ : List Ty} :
    OrdinalExpression (Ty.curriedGround (k+1) :: Γ) → List Carrier → Nat → Prop where
  | free {q} (inactive : ¬ Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q) :
      Account q [] 1
  | tracked : Account (.var ⟨_,.here,0⟩) [] 1
  | add {a b xs ys c d}
      (active : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (.add a b))
      (left : Account a xs c) (right : Account b ys d) :
      Account (.add a b) (xs ++ ys) (c+d+1)
  | finite {h t} {xs : List Carrier} {c n : Nat}
      (active : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (.collapse h t))
      (finite : unitValue h = (n : Ordinal)) (tail : Account t xs c) :
      Account (.collapse h t) xs (c+n+HeadFiniteSurplus.surplus h)
  | nonfinite {h t xs c} (label : Carrier)
      (active : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (.collapse h t))
      (nonfinite : Ordinal.omega0 ≤ unitValue h) (exactHead : label.head = unitValue h)
      (tail : Account t xs c) :
      Account (.collapse h t) (xs ++ [label]) (c+HeadFiniteSurplus.surplus h)
end LogicLineages.OrdinalComparison.Source.ScalarCarrierAccounting
