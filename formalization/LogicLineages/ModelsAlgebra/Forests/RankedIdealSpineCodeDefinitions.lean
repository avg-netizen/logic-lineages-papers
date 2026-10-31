module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealSpineDefinitions
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularCodeDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealSpineCode
open RankedParse RankedIdealRank RankedIdealComponents RankedIdealCompletion RankedIdealRegularCode RankedGraphImage
instance sameDecidable (C : Code) (p q : C.machine.State) : Decidable (SameComponent C.machine p q) :=
  inferInstanceAs (Decidable (_ ∈ RankedIdealFinite.close C.machine {_} ∧ _ ∈ RankedIdealFinite.close C.machine {_}))
instance lowerDecidable (C : Code) (p q : C.machine.State) : Decidable (Lower C.machine p q) :=
  inferInstanceAs (Decidable (_ ∈ RankedIdealFinite.close C.machine {_} ∧ _ ∉ RankedIdealFinite.close C.machine {_}))
def ops : List Operation := [.union, .join]
def leftOK (C : Code) (q : C.machine.State) (o : Operation) (x y : C.machine.State) : Prop :=
  x ∈ productive C.machine ∧ y ∈ productive C.machine ∧
  SameComponent C.machine q (C.machine.node o x y) ∧
  SameComponent C.machine q x ∧ Lower C.machine y q
def rightOK (C : Code) (q : C.machine.State) (o : Operation) (x y : C.machine.State) : Prop :=
  x ∈ productive C.machine ∧ y ∈ productive C.machine ∧
  SameComponent C.machine q (C.machine.node o x y) ∧
  Lower C.machine x q ∧ SameComponent C.machine q y
instance leftDecidable C q o x y : Decidable (leftOK C q o x y) := by unfold leftOK; infer_instance
instance rightDecidable C q o x y : Decidable (rightOK C q o x y) := by unfold rightOK; infer_instance
/-- Every actual one-spine transition is enumerated from explicit input lists. -/
def frames (C : Code) (q : C.machine.State) : List Rule :=
  ops.flatMap fun o => C.states.flatMap fun x => C.states.flatMap fun y =>
    (if leftOK C q o x y then [⟨o,true,component C y⟩] else []) ++
    (if rightOK C q o x y then [⟨o,false,component C x⟩] else [])
def alphabet (C : Code) (q : C.machine.State) :=
  RankedIdealRegular.allowed (fun i : Fin (frames C q).length => viewRule ((frames C q)[i]))
def nodeOK (C : Code) (q : C.machine.State) (o : Operation) (x y : C.machine.State) : Prop :=
  x ∈ productive C.machine ∧ y ∈ productive C.machine ∧
  SameComponent C.machine q (C.machine.node o x y) ∧ Lower C.machine x q ∧ Lower C.machine y q
instance nodeDecidable C q o x y : Decidable (nodeOK C q o x y) := by unfold nodeOK; infer_instance
/-- Ground entry compiler, parameterized only by structurally smaller recursive outputs. -/
def seeds (C : Code) (q : C.machine.State) (rec : C.machine.State → List Code) : List Code :=
  (if SameComponent C.machine q C.machine.leaf then [atom] else []) ++
  C.states.flatMap (fun p => if Lower C.machine p q then rec p else []) ++
  ops.flatMap (fun o => C.states.flatMap (fun x => C.states.flatMap (fun y =>
    if nodeOK C q o x y then (rec x).flatMap (fun A => (rec y).map (product o A)) else [])))
def LowerCorrect (C : Code) (q : C.machine.State) (rec : C.machine.State → List Code) : Prop :=
  ∀ p, Lower C.machine p q →
    (∀ B ∈ rec p, IsIdeal (language B)) ∧
    ∀ t, (∃ B ∈ rec p, language B t) ↔ Run C.machine t p
end LogicLineages.ModelsAlgebra.Forests.RankedIdealSpineCode
