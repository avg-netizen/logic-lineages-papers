module
public import LogicLineages.OrdinalComparison.WWSourceRenamingDefinitions
public import LogicLineages.OrdinalComparison.SourceTypedPortsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SelectedBinder

/-- Exchange precisely the first two typed names. -/
def swap {Γ : List Ty} {σ τ : Ty} : Renaming (σ :: τ :: Γ) (τ :: σ :: Γ)
  | _, .here => .there .here
  | _, .there .here => .here
  | _, .there (.there x) => .there (.there x)

/-- Move the selected occurrence to the head, leaving all other names in their
original relative order. Equal types do not identify different names. -/
def moveToHead (left right : List Ty) (σ : Ty) :
    Renaming (left ++ σ :: right) (σ :: (left ++ right)) :=
  match left with
  | [] => fun x => x
  | _ :: left => fun x => swap (Renaming.lift (moveToHead left right σ) x)

def moveFromHead (left right : List Ty) (σ : Ty) :
    Renaming (σ :: (left ++ right)) (left ++ σ :: right) :=
  match left with
  | [] => fun x => x
  | _ :: left => fun x => Renaming.lift (moveFromHead left right σ) (swap x)

def selected (left right : List Ty) (σ : Ty) : Variable (left ++ σ :: right) σ :=
  match left with
  | [] => .here
  | _ :: left => .there (selected left right σ)

/-- Actual source abstraction after capture-free typed permutation. Renaming
is lifted under every internal lambda, of any type. -/
def boundSource {left right : List Ty} {σ τ : Ty}
    (t : OriginalTerm (left ++ σ :: right) τ) : OriginalTerm (left ++ right) (.arrow σ τ) :=
  .lam (t.rename (moveToHead left right σ))

/-- Transport the single shared valuation through the inverse permutation;
this never introduces independent copies of an old shared name. -/
def transport {α : Type} (left right : List Ty) (σ : Ty)
    (ρ : OrdinalComponent (left ++ σ :: right) → α) :
    OrdinalComponent (σ :: (left ++ right)) → α :=
  fun c => ρ (ordinalComponentRename (moveFromHead left right σ) c)
end LogicLineages.OrdinalComparison.Source.SelectedBinder
