module
public import LogicLineages.StandardControlCurrent.PolicyAssignmentDefinitions
public import LogicLineages.StandardControlCurrent.PolicyIndexedRankedLayerTargets
public import LogicLineages.StandardControlCurrent.PolicyIndexedShapeTargets

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedAssignment
open OrdinalComparison Source Source.AdmissibleSum Source.SyntaxCode Source.OrdinalSyntax
open Nat.Partrec (Code)

abbrev Node := List Nat × Nat
abbrev Value := Option (List Nat)
abbrev Args := Node × List Value
abbrev Abstraction := Code → Nat → Nat → List Nat → Part Value

def ImplementsAbstraction (backend : Abstraction) (c : Code) (p : Policy) : Prop :=
  ∀ inputLevel bodyLevel body, backend c inputLevel bodyLevel body =
    Part.some (PolicyAbstraction.abstractionCode p inputLevel bodyLevel body)

def rank (s : Node) : Nat := s.2

def children (s : Node) : List Node :=
  if s.2%8=5 then [(s.1,(s.2/8).unpair.1),(s.1,(s.2/8).unpair.2)]
  else if s.2%8=6 then [((s.2/8).unpair.1::s.1,(s.2/8).unpair.2)] else []

def recursorFrom (inputLevel resultLevel two : Nat) : List Nat :=
  (List.range (resultLevel+1)).map (fun i =>
    if i=0 then two else if i=inputLevel+2 then 2 else 1)

def applicationFrom (resultLevel argLevel : Nat) (f g : List Nat) (tail : Nat) : List Nat :=
  (List.range (resultLevel+1)).map (fun i => if i=0 then
    node 6 (boxPositive argLevel f g 1) tail else boxPositive argLevel f g i)

noncomputable def numeral (c : Code) (n : Nat) : Part (Option Nat) :=
  if n=0 then Part.some (some 0) else
    PolicyIndexedShape.macroCode (c,PolicyShape.siteCode .numeral,n-1,List.replicate n 1)

noncomputable def tailCode (c : Code) (n f g : Nat) : Part (Option Nat) :=
  if n=0 then Part.some (some (node 4 f g))
  else (numeral c n).bind fun
    | none => Part.some none
    | some num => PolicyIndexedShape.macroCode (c,PolicyShape.siteCode .optionalBoxTail,2,[f,g,num])

/-- Source check and binder/context protocol are independent of the
choice of the real indexed abstraction implementation. -/
def body {F : Type} (lift : Value → F)
    (rec : Nat → Nat → F) (app : Nat → Nat → List Nat → List Nat → F)
    (lam : Nat → Nat → List Nat → F) (s : Node) (rs : List Value) : F :=
  match check s.1 s.2 with
  | none => lift none
  | some resultType =>
    let n := s.2
    let q := (n/8).unpair
    if n%8<5 then
      if n%8=0 then lift (some ((List.range (typeLevel resultType+1)).map
        (fun i => 8*Nat.pair (n/8) i+3)))
      else if n%8=4 then rec (typeLevel (n/8)) (typeLevel resultType)
      else lift (some (List.replicate (typeLevel resultType+1) 1))
    else if n%8=5 then
      match check s.1 q.2, rs.getD 0 none, rs.getD 1 none with
      | some ty, some f, some g => app (typeLevel resultType) (typeLevel ty) f g
      | _, _, _ => lift none
    else if n%8=6 then
      match check (q.1::s.1) q.2, rs.getD 0 none with
      | some ty, some b => lam (typeLevel q.1) (typeLevel ty) b
      | _, _ => lift none
    else lift none

def typedNode (p : Policy) (s : Node) (rs : List Value) : Option Value :=
  some (body id (PolicyConstructors.recursorCode p) (PolicyConstructors.applicationCode p)
    (PolicyAbstraction.abstractionCode p) s rs)

noncomputable def assemble (backend : Abstraction) (c : Code) (x : Args) : Part (Option Value) :=
  (body Part.some
    (fun input output => (numeral c 2).map (Option.map (recursorFrom input output)))
    (fun output arg f g =>
      (tailCode c arg (f.getD 0 0) (g.getD 0 0)).map (Option.map (applicationFrom output arg f g)))
    (backend c) x.1 x.2).map some

noncomputable def run (backend : Abstraction) (p : Code × Node) : Part (Option Value) :=
  PolicyIndexedRankedGraph.root rank children
    (PolicyIndexedRankedLayer.layer children (assemble backend)) p

def ExactIndexedAssignmentNode : Prop :=
  (∀ s, ∀ t ∈ children s, rank t < rank s) ∧
  (∀ p : Policy, ∀ s : Node,
    typedNode p s ((children s).map (fun q => PolicyAssignment.assignmentCode p q.1 q.2)) =
      some (PolicyAssignment.assignmentCode p s.1 s.2)) ∧
  ∀ (backend : Abstraction) (c : Code) (p : Policy), PolicyIndexedShape.Implements c p →
    ImplementsAbstraction backend c p → ∀ s rs,
      assemble backend c (s,rs) = Part.some (typedNode p s rs)

def ExactIndexedAssignmentRun : Prop :=
  ∀ (backend : Abstraction) (c : Code) (p : Policy), PolicyIndexedShape.Implements c p →
    ImplementsAbstraction backend c p → ∀ s,
      run backend (c,s) = Part.some (some (PolicyAssignment.assignmentCode p s.1 s.2))

end LogicLineages.StandardControlCurrent.PolicyIndexedAssignment
