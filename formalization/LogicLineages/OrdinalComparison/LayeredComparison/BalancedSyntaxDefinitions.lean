module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerSyntaxDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedRowDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedSyntax
open CommonLayerSyntax

/-- The fixed k-entry common basis occurs positively in EVERY head argument.
A stored factor a represents a+1, exactly the original positive grammar. -/
structure Atom (k:Nat) where
  head:NONote
  offset:Nat
  factors:Fin k→Nat

/-- One literal source level. Outside coefficients may vanish; each listed
atom has positive outer coefficient q+1, so zero multiples have been removed. -/
structure Upper (k:Nat) where
  constant:Nat
  outside:Fin k→Nat
  atoms:List (Nat×Atom k)

/-- A finite shape records the common-basis size at each successive level. -/
def Syntax:List Nat→Type
  | []=>BaseTerm
  | k::_=>Upper k

/-- At each positive level there is ONE shared preceding certificate and ONE
whole ordered basis, permitting repeated/dependent entries. No independently
valued rawVariables are added for basis entries. -/
def Certificate:List Nat→Type
  | []=>Unit
  | k::Γ=>Certificate Γ×(Fin k→Syntax Γ)

noncomputable def asAtom {k:Nat} (a:Atom k):BalancedRow.Atom:=
  ⟨a.head,a.offset,List.ofFn (fun j=>a.factors j+1)⟩

noncomputable def value:(Γ:List Nat)→Certificate Γ→Syntax Γ→(Nat→Nat)→Nat
  | [],_,E,ν=>E.value ν
  | k::Γ,C,E,ν=>
    let basis:=List.ofFn (fun j:Fin k=>value Γ C.1 (C.2 j) ν)
    E.constant+((List.ofFn E.outside).zipWith (·*·) basis).sum+
      (E.atoms.map (fun a=>(a.1+1)*actualHeadValue a.2.head.1.repr
        (BalancedRow.input basis (asAtom a.2)))).sum

/-- Actual syntax support: zero outside multiples contribute NO rawVariables;
EVERY listed positive atom contributes the WHOLE shared basis support. -/
def rawVariables:(Γ:List Nat)→Certificate Γ→Syntax Γ→List Nat
  | [],_,E=>E.variables
  | k::Γ,C,E=>
    let bv:=fun j:Fin k=>rawVariables Γ C.1 (C.2 j)
    (List.finRange k).flatMap (fun j=>if E.outside j=0 then [] else bv j)++
      E.atoms.flatMap (fun _=>(List.finRange k).flatMap bv)

def genuineExpression:(Γ:List Nat)→Syntax Γ→Prop
  | [],_=>True
  | _::_,E=>∀a∈E.atoms,Order.IsSuccLimit a.2.head.1.repr

def genuineCertificate:(Γ:List Nat)→Certificate Γ→Prop
  | [],_=>True
  | _::Γ,C=>genuineCertificate Γ C.1∧∀j,genuineExpression Γ (C.2 j)

noncomputable def basisValues (k:Nat) (Γ:List Nat) (C:Certificate (k::Γ)) (ν:Nat→Nat):List Nat:=
  List.ofFn (fun j:Fin k=>value Γ C.1 (C.2 j) ν)

/-- Literal signed row of a whole source pair; the outside remainder uses the
SAME common basis as EVERY positive head argument on BOTH sides. -/
noncomputable def comparisonRow {k:Nat} (E F:Upper k):BalancedRow.Row:=
  ⟨(E.constant:Int)-(F.constant:Int),
    List.ofFn (fun j=>(E.outside j:Int)-(F.outside j:Int)),
    E.atoms.map (fun a=>((a.1+1:Int),asAtom a.2))++
      F.atoms.map (fun a=>(-((a.1+1:Int)),asAtom a.2))⟩
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedSyntax
