module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowHeadEnumerationTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimaryCoverSyntax
open NumberedWindowSyntax NumberedWindowHeadEnumerationTargets

/-- Measures on the actual numerical syntax. The first counts constructor
nodes (one per term and one per nonempty argument cell). The second is
the maximum of the actual free indices, bound indices and finite labels.
Original ranked codes and polymorphic head parameter types are separate
components of the admitted head alphabet and are not counted as numerals. -/
structure Bounds where
  nodes : Nat
  numeral : Nat

mutual
def termBounds : NTerm → Bounds
  | .free _ x | .bound _ x => ⟨1,x⟩
  | .bottom _ => ⟨1,0⟩
  | .lam _ Q =>
    let b := termBounds Q
    ⟨b.nodes + 1,b.numeral⟩
  | .ordinary _ bs =>
    let b := argsBounds bs
    ⟨b.nodes + 1,b.numeral⟩
  | .numbered _ _ k bs es =>
    let b := argsBounds bs
    let e := argsBounds es
    ⟨b.nodes + e.nodes + 1,max k (max b.numeral e.numeral)⟩
  | .auxApp _ _ Q A =>
    let b := termBounds Q
    let a := termBounds A
    ⟨b.nodes + a.nodes + 1,max b.numeral a.numeral⟩

def argsBounds : NArgs → Bounds
  | .nil => ⟨0,0⟩
  | .cons Q qs =>
    let b := termBounds Q
    let a := argsBounds qs
    ⟨b.nodes + 1 + a.nodes,max b.numeral a.numeral⟩
end

def leaves (K : List Ty) (numerals : List Nat) : List NTerm :=
  (K.flatMap fun σ => numerals.map (NTerm.free σ)) ++
  (K.flatMap fun σ => numerals.map (NTerm.bound σ)) ++ K.map NTerm.bottom

def lambdas (K : List Ty) (terms : List NTerm) : List NTerm :=
  K.flatMap fun σ => terms.map (NTerm.lam σ)

def ordinaryHeads (H : List Head) (args : List NArgs) : List NTerm :=
  H.flatMap fun f => args.map (NTerm.ordinary f)

def numberedHeads (H : List Head) (K : List Ty) (numerals : List Nat)
    (args : List NArgs) : List NTerm :=
  H.flatMap fun f => K.flatMap fun τ => numerals.flatMap fun k =>
    args.flatMap fun bs => args.map (NTerm.numbered f τ k bs)

def auxiliaryApps (K : List Ty) (terms : List NTerm) : List NTerm :=
  K.flatMap fun σ => K.flatMap fun τ =>
    terms.flatMap fun Q => terms.map (NTerm.auxApp σ τ Q)

def argumentCells (terms : List NTerm) (args : List NArgs) : List NArgs :=
  .nil :: (terms.flatMap fun Q => args.map (NArgs.cons Q))

/-- Finite constructor-only cover grammar. At positive fuel, all recursive
children come from the preceding layer. This intentionally lists a finite
superset, not a test for typing or for primary equivalence. -/
def grammar (H : List Head) (K : List Ty) (maxNumeral : Nat) :
    Nat → List NTerm × List NArgs
  | 0 => ([],[.nil])
  | n + 1 =>
    let (ts,as) := grammar H K maxNumeral n
    let numerals := List.range (maxNumeral + 1)
    (leaves K numerals ++ lambdas K ts ++ ordinaryHeads H as ++
     numberedHeads H K numerals as ++ auxiliaryApps K ts,
     argumentCells ts as)

/-- On the same original fixed admitted head window and type list, the
source term's actual two measures choose a finite executable candidate
list. Heads retain their original declarations, including retyped ones. -/
def cover (S : Spine.Signature) (K : List Ty) (Q : NTerm) : List NTerm :=
  let b := termBounds Q
  (grammar (admittedHeads S K) K b.numeral b.nodes).1

end LogicLineages.PersistentMarking.NumberedWindowPrimaryCoverSyntax
