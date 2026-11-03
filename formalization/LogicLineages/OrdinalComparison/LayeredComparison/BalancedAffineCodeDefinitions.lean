module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineSyntaxDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedEvaluationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineCode
open BalancedEvaluation

/-- The existing AtomData payload, with the same ordinary Encodable codec used
inside encoded upper expressions. A failed raw decode has an explicit default. -/
def atomData (code : Nat) : AtomData :=
  (Encodable.decode code).getD (0,0,0,[])

/-- Literal numeral encoding at the requested shape, including the BASE case. -/
def numeral : List Nat → Nat → Nat
  | [], n => 4*n
  | k::_, n => Encodable.encode ((n,List.replicate k 0,[]) : UpperData)

/-- Upper addition retains the ordered atom payloads verbatim, including their
stored positive coefficients and duplicates. Outside vectors have exactly k
entries; missing raw entries default to zero and excess entries are ignored. -/
def add : List Nat → Nat → Nat → Nat
  | [], E, F => 4*Nat.pair E F+2
  | k::_, E, F =>
    let e := upperData E
    let f := upperData F
    Encodable.encode ((e.1+f.1,
      (List.range k).map (fun j => e.2.1.getD j 0+f.2.1.getD j 0),
      e.2.2++f.2.2) : UpperData)

/-- The same literal repeated-addition tree as Affine.scale. In particular,
zero uses the shape's zero numeral and carries no atom payloads. -/
def scale (Γ : List Nat) (n E : Nat) : Nat :=
  (List.replicate n E).foldr (add Γ) (numeral Γ 0)

/-- A literal ordered k-entry affine combination of numeric basis codes.
Missing coefficients and basis codes default to zero; extra entries are ignored.
No independent valuation or head evaluation occurs in this constructor. -/
def combination (Γ : List Nat) (k c : Nat) (coefficients basis : List Nat) : Nat :=
  add Γ (numeral Γ c)
    (((List.range k).map (fun j => scale Γ (coefficients.getD j 0) (basis.getD j 0))).foldr
      (add Γ) (numeral Γ 0))

/-- The actual preceding-level outside expression uses the encoded original
certificate's own ordered basis, not a newly supplied family of variables. -/
def lowerPart (k : Nat) (Γ : List Nat) (C E : Nat) : Nat :=
  combination Γ k (upperData E).1 (upperData E).2.1 (certificateData C).2

/-- Complete input constructor. The stored outer atom coefficient is irrelevant
to the input; EVERY stored factor denotes factor+1. Its only ordinal operation
is the existing rawNormCode, also on malformed raw head codes. -/
noncomputable def completeInput (k : Nat) (Γ : List Nat) (C a : Nat) : Nat :=
  let data := atomData a
  combination Γ k (rawNormCode data.2.1+data.2.2.1)
    ((List.range k).map (fun j => data.2.2.2.getD j 0+1)) (certificateData C).2

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineCode
