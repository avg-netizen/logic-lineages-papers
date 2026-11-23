module
public import LogicLineages.StandardControlCurrent.PolicyIndexedShapeTargets
public import LogicLineages.StandardControlCurrent.PolicyAbstractionDefinitions

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedAbstractionPartials
open OrdinalComparison.Source.AdmissibleSum (Policy)
open OrdinalComparison.Source.OrdinalSyntax (collectLists)
open Nat.Partrec (Code)

abbrev Args := Code × Nat × Nat × List Nat
abbrev PartialArgs := Code × Nat × Nat × Nat
abbrev PartialBackend := PartialArgs → Part (Option (List Nat))

/-- Agreement includes returned refusals, not merely successful values. -/
def ImplementsPartial (run : PartialBackend) (c : Code) (p : Policy) : Prop :=
  ∀ (level i n : Nat), run (c,level,i,n) = Part.some (PolicyPartial.run p level i n)

/-- Apply the indexed partial to the literal body coordinate, at that coordinate's
grade. The result depth m does not replace the input level or grade. -/
def callArgs (a : Args) (i : Nat) : PartialArgs :=
  (a.1,a.2.1,i,a.2.2.2.getD i 0)

noncomputable def prefixCode (run : PartialBackend) (a : Args) (k : Nat) :
    Part (List (Option (List Nat))) :=
  k.rec (Part.some []) fun i ih => ih.bind fun rs =>
    (run (callArgs a i)).map (fun r => rs ++ [r])

/-- Execute the literal m+1 calls in order before handing returned Options to
the original refusing collector. This makes no adequacy claim for an index on
which an eagerly evaluated call diverges. -/
noncomputable def partialsCode (run : PartialBackend) (a : Args) : Part (Option (List (List Nat))) :=
  (prefixCode run a (a.2.2.1 + 1)).map collectLists

def ExactPartials : Prop :=
  ∀ (run : PartialBackend) (c : Code) (p : Policy), ImplementsPartial run c p →
    ∀ (level m : Nat) (h : List Nat),
      partialsCode run (c,level,m,h) = Part.some (PolicyAbstraction.partialsCode p level m h)

def IndexedPartialsPartrec : Prop :=
  ∀ (run : PartialBackend), Partrec run → Partrec (partialsCode run)

end LogicLineages.StandardControlCurrent.PolicyIndexedAbstractionPartials
