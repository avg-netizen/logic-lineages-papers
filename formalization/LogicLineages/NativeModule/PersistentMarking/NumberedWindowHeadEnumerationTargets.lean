module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowDomain

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowHeadEnumerationTargets
open NumberedWindowDomain

/-- Candidate heads are the actual native head constructors, K-induced
type parameters for polymorphic native and application heads, and the
original ranked signature declarations. Variable/bottom/auxApp are
not head symbols and do not occur here. -/
def candidates (S : Spine.Signature) (K : List Ty) : List Head :=
  ([.zero,.succ] : List Head) ++ K.map Head.case ++ K.map Head.recursor ++
    K.flatMap (fun σ => K.map (Head.app σ)) ++
    S.entries.map (fun p => Head.ranked p.1 p.2)

def headBit (S : Spine.Signature) (K : List Ty) (f : Head) : Bool :=
  (Spine.classRank S f).isSome &&
    (DecisionInventory.declaration f).all (fun τ => decide (τ ∈ K))

/-- Deduplicate by literal Head equality, not by head rank/class.
Distinct admitted native/ranked/application heads stay distinct. -/
def unique : List Head → List Head
  | [] => []
  | f::fs => if f ∈ fs then unique fs else f :: unique fs

def admittedHeads (S : Spine.Signature) (K : List Ty) : List Head :=
  unique ((candidates S K).filter (headBit S K))

/-- Restrict the literal admitted list using the original classRank.
The test does not add a different signature or equate different heads
by name instead of the manuscript's specified precedence class. -/
def equivalentHeads (S : Spine.Signature) (K : List Ty) (f : Head) : List Head :=
  (admittedHeads S K).filter (fun g => decide (Spine.classRank S f = Spine.classRank S g))

def HeadBitExact : Prop := ∀ S K f,
  headBit S K f = true ↔ HeadInWindow S K f

def AdmittedHeadEnumeration : Prop := ∀ S K,
  (admittedHeads S K).Nodup ∧
    ∀ f, f ∈ admittedHeads S K ↔ HeadInWindow S K f

def EquivalentHeadEnumeration : Prop := ∀ S K f,
  (equivalentHeads S K f).Nodup ∧
    ∀ g, g ∈ equivalentHeads S K f ↔ HeadInWindow S K g ∧ Spine.Equivalent S f g

end LogicLineages.PersistentMarking.NumberedWindowHeadEnumerationTargets
