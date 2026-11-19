import LogicLineages.PersistentMarking.NumberedWindowHeadEnumerationTargets

namespace LogicLineages.PersistentMarking.NumberedWindowTypingBits
open Spine NumberedWindowSyntax NumberedWindowDomain
open NumberedWindowHeadEnumerationTargets (headBit)

/-- Actual finite, nearest-binder-first representation. Typed free names
are globally available pairs and are not additional bound lookup slots. -/
def binderLookup (Γ : List Ty) : BoundContext :=
  fun i => Γ[i]?

def annotationList (qs : NArgs) : List Ty := qs.toList.map NTerm.type

/- The abstract C parameter supplies only the existing bound-variable
lookup. For ordinary and numbered heads, the base annotations must
literally match the head's original argument declaration. -/
mutual
def termOK (C : BoundContext) : NTerm → Bool
  | .free _ _ | .bottom _ => true
  | .bound σ i => decide (C i = some σ)
  | .lam σ Q => termOK (C.push σ) Q
  | .ordinary f bs => decide (annotationList bs = f.arguments) && argsOK C bs
  | .numbered f _ _ bs es =>
    decide (annotationList bs = f.arguments) && argsOK C bs && argsOK C es
  | .auxApp σ τ Q A =>
    decide (Q.type = .arrow σ τ) && termOK C Q &&
    decide (A.type = σ) && termOK C A

def argsOK (C : BoundContext) : NArgs → Bool
  | .nil => true
  | .cons Q qs => termOK C Q && argsOK C qs
end

def typedBit (C : BoundContext) (τ : Ty) (Q : NTerm) : Bool :=
  decide (Q.type = τ) && termOK C Q

def baseBit (C : BoundContext) (types : List Ty) (qs : NArgs) : Bool :=
  decide (annotationList qs = types) && argsOK C qs

def extrasBit (C : BoundContext) (qs : NArgs) : Bool := argsOK C qs

def windowBit (S : Signature) (K : List Ty) (C : BoundContext) (τ : Ty) (Q : NTerm) :
    Bool :=
  typedBit C τ Q &&
    (support Q).all (fun σ => decide (σ ∈ K)) &&
    (heads Q).all (headBit S K)

/-- Executable use takes a finite binder stack, not an encoding of an
arbitrary functional C. Unused entries are not added to term support. -/
def finiteWindowBit (S : Signature) (K : List Ty) (Γ : List Ty) (τ : Ty) (Q : NTerm) :
    Bool :=
  windowBit S K (binderLookup Γ) τ Q

end LogicLineages.PersistentMarking.NumberedWindowTypingBits
