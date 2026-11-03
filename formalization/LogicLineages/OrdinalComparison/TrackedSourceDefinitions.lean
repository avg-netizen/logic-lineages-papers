module
public import LogicLineages.OrdinalComparison.SourceFreeOccurrencesDefinitions
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentDefinitions
public import LogicLineages.OrdinalComparison.WWDefaultPolicyDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.TrackedSource
open SourceFreeOccurrences

/-- Literal paper09 generated grammar. The tracked function is non-ground.
Only the RESULT of an opaque block has level at most one; its internal source
syntax is unrestricted and may capture the surrounding ground variables. -/
inductive Expr (k : Nat) : (Γ : List Ty) → Variable Γ (Ty.curriedGround (k+1)) → Nat → Type where
  | tracked {Γ F} : Expr k Γ F (k+1)
  | ground {Γ F} (x : Variable Γ .ground) : Expr k Γ F 0
  | free {Γ F n} (t : OriginalTerm Γ (Ty.curriedGround n))
      (hfree : (⟨Ty.curriedGround (k+1),F⟩ : PackedVariable Γ) ∉ freeOccurrences t) : Expr k Γ F n
  | app {Γ F n} (f : Expr k Γ F (n+1)) (a : Expr k Γ F 0) : Expr k Γ F n
  | lam {Γ F n} (body : Expr k (.ground :: Γ) (.there F) n) : Expr k Γ F (n+1)

def erase {k Γ F n} : Expr k Γ F n → OriginalTerm Γ (Ty.curriedGround n)
  | .tracked=>.var F
  | .ground x=>.var x
  | .free t _=>t
  | .app f a=>.app (erase f) (erase a)
  | .lam body=>.lam (erase body)

def occurrences {k Γ F n} : Expr k Γ F n → List (PackedVariable Γ)
  | .tracked=>[⟨_,F⟩]
  | .ground x=>[⟨_,x⟩]
  | .free t _=>freeOccurrences t
  | .app f a=>occurrences f++occurrences a
  | .lam body=>(occurrences body).filterMap dropBound

def active {k Γ F n} : Expr k Γ F n → Bool
  | .tracked=>true
  | .ground _ | .free _ _=>false
  | .app f a=>active f || active a
  | .lam body=>active body

/-- The same source closure stated directly on actual original terms, to make
coverage of the complete grammar an independently checked erasure contract. -/
inductive Generated (k : Nat) : {Γ : List Ty} → (F : Variable Γ (Ty.curriedGround (k+1))) →
    {n : Nat} → OriginalTerm Γ (Ty.curriedGround n) → Prop where
  | tracked {Γ F} : @Generated k Γ F (k+1) (.var F)
  | ground {Γ F} (x : Variable Γ .ground) : @Generated k Γ F 0 (.var x)
  | free {Γ F n} (t : OriginalTerm Γ (Ty.curriedGround n))
      (hfree : (⟨Ty.curriedGround (k+1),F⟩ : PackedVariable Γ) ∉ freeOccurrences t) : Generated k F t
  | app {Γ F n} {f : OriginalTerm Γ (Ty.curriedGround (n+1))} {a : OriginalTerm Γ .ground}
      (hf : @Generated k Γ F (n+1) f) (ha : @Generated k Γ F 0 a) : @Generated k Γ F n (.app f a)
  | lam {Γ F n} {body : OriginalTerm (.ground :: Γ) (Ty.curriedGround n)}
      (hb : @Generated k (.ground :: Γ) (.there F) n body) : @Generated k Γ F (n+1) (.lam body)
end LogicLineages.OrdinalComparison.Source.TrackedSource
