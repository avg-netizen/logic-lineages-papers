module
public import LogicLineages.StandardControlCurrent.PolicyIndexedRankedLayerTargets
public import LogicLineages.StandardControlCurrent.PolicyIndexedMergeTargets

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedPartial
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax
open Nat.Partrec (Code)

abbrev Node := Nat × Nat × Nat
abbrev Value := Option (List Nat)
abbrev Args := Node × List Value

def rank (s : Node) : Nat := s.2.2

def active (n : Nat) : Prop := n%8 = 4 ∨ n%8 = 5 ∨ n%8 = 6

instance (n : Nat) : Decidable (active n) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def children (s : Node) : List Node :=
  if active s.2.2 then
    [(s.1, (if s.2.2%8=4 then s.2.1 else if s.2.2%8=5 then s.2.1+1 else 1), (s.2.2/8).unpair.1),
     (s.1, (if s.2.2%8=6 then 0 else s.2.1), (s.2.2/8).unpair.2)]
  else []

def childPair (xs : List Value) : Option (List Nat × List Nat) := do
  let a ← xs.getD 0 none
  let b ← xs.getD 1 none
  pure (a,b)

def typedMerge (p : Policy) (level tag : Nat) (xs : List Value) : Value :=
  (childPair xs).bind (fun ab => PolicyPartial.mergeCode p level tag ab.1 ab.2)

noncomputable def indexedMerge (c : Code) (level tag : Nat)
    (xs : List Value) : Part Value :=
  match childPair xs with
  | none => Part.some none
  | some ab => PolicyIndexedMerge.merge (c,level,tag,ab.1,ab.2)

def collapse (s : Node) (xs : List Value) : Value :=
  (childPair xs).map (fun ab => partialCollapse s.1 (s.2.2/8).unpair.1 ab.1 ab.2)

/-- Original ranked assembly shared by the typed and indexed paths. The
whole-head-free test has precedence over tag-based dispatch. -/
def caseBody {F : Type} (lift : Value → F) (join : Nat → Nat → List Value → F)
    (s : Node) (xs : List Value) : F :=
  if headFree s.2.2 then lift (some (partialFree s.1 s.2.1 s.2.2))
  else if s.2.2%8 = 3 then
    if s.2.1 = (s.2.2/8).unpair.2 then lift (some (List.replicate (s.1+2) 1)) else lift none
  else if active s.2.2 then
    if s.2.2%8 = 4 then join s.1 4 xs
    else if s.2.2%8 = 5 then
      if 0 < s.2.1 then join s.1 5 xs else lift none
    else if s.2.1 = 0 then lift (collapse s xs) else lift none
  else lift none

def typedNode (p : Policy) (s : Node) (xs : List Value) : Option Value :=
  some (caseBody id (typedMerge p) s xs)

noncomputable def assemble (c : Code) (x : Args) : Part (Option Value) :=
  (caseBody Part.some (indexedMerge c) x.1 x.2).map some

noncomputable def run (p : Code × Node) : Part (Option Value) :=
  PolicyIndexedRankedGraph.root rank children (PolicyIndexedRankedLayer.layer children assemble) p

def ExactIndexedPartialNode : Prop :=
  (∀ s, ∀ child ∈ children s, rank child < rank s) ∧
  (∀ p : Policy, ∀ s : Node,
    typedNode p s ((children s).map (fun q => PolicyPartial.run p q.1 q.2.1 q.2.2)) =
      some (PolicyPartial.run p s.1 s.2.1 s.2.2)) ∧
  ∀ (c : Code) (p : Policy), PolicyIndexedShape.Implements c p → ∀ s xs,
    assemble c (s,xs) = Part.some (typedNode p s xs)

def ExactIndexedPartialRun : Prop :=
  ∀ (c : Code) (p : Policy), PolicyIndexedShape.Implements c p → ∀ s : Node,
    run (c,s) = Part.some (some (PolicyPartial.run p s.1 s.2.1 s.2.2))

end LogicLineages.StandardControlCurrent.PolicyIndexedPartial
