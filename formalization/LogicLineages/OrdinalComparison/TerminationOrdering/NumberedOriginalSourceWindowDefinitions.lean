module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourcePresentationProof
public import LogicLineages.OrdinalComparison.SourcePortContextsDefinitions

@[expose] public section
/-! Exact literal source type windows. The traversal retains duplicates and
ranked argument order. It is defined on all structural codes; malformed codes
have total fallback behavior, while calibration is to actual original terms.
The primitive-recursive claim is a separate target, not part of the definition.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceWindow
open Source NumberedAuxiliaryCoding NumberedRewriteSyntax

def resultType : Ty → Ty
  | .ground => .ground
  | .arrow _ tau => tau

mutual
def termWindow {Symbol : Type} (tau : Ty) : Code Symbol → List Ty
  | .var _ | .bottom _ | .argumentsNil | .argumentsCons _ _ _ => tau.subtypes
  | .lam _ body => tau.subtypes ++ termWindow (resultType tau) body
  | .app sigma f a => tau.subtypes ++ (termWindow (.arrow sigma tau) f ++ termWindow sigma a)
  | .ordinary _ base => tau.subtypes ++ argumentsWindow base
  | .numbered _ _ _ base _ extras => tau.subtypes ++ (argumentsWindow base ++ argumentsWindow extras)
def argumentsWindow {Symbol : Type} : Code Symbol → List Ty
  | .argumentsCons sigma q rest => termWindow sigma q ++ argumentsWindow rest
  | _ => []
end

abbrev Request (n : Nat) := Sum (Ty × Code (Fin n)) (Code (Fin n))

def requestValue {n : Nat} : Request n → List Ty
  | .inl (tau,code) => termWindow tau code
  | .inr code => argumentsWindow code

def requestCode {n : Nat} : Request n → Code (Fin n)
  | .inl (_,code) | .inr code => code

def requests {n : Nat} : Request n → List (Request n)
  | .inl (tau,.lam _ body) => [.inl (resultType tau,body)]
  | .inl (tau,.app sigma f a) => [.inl (.arrow sigma tau,f),.inl (sigma,a)]
  | .inl (_,.ordinary _ base) => [.inr base]
  | .inl (_,.numbered _ _ _ base _ extras) => [.inr base,.inr extras]
  | .inr (.argumentsCons sigma q rest) => [.inl (sigma,q),.inr rest]
  | _ => []

def rootTypes {n : Nat} : Request n → List Ty
  | .inl (tau,_) => tau.subtypes
  | .inr _ => []

def recombine {n : Nat} (request : Request n) (values : List (List Ty)) : Option (List Ty) :=
  some (rootTypes request ++ values.flatten)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceWindow
