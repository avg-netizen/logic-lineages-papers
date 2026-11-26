module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowClosing
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowTupleTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowFrameTargets
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowPrimary
open NumberedWindowClosing NumberedWindowPreservationTargets NumberedWindowTupleTargets
open NameBridge (Name freeOccurs)

/- Closing preserves the exact annotation and inventories, not just a
syntactic shape relation with an opportunity to discard a declaration. -/
def ClosingInventories : Prop := ∀ (name : Name) d (q : NTerm),
  (closeAt name d q).type = q.type ∧
  support (closeAt name d q) = support q ∧ heads (closeAt name d q) = heads q

def ClosingLexicalAdmissibility : Prop := ∀ S K name d (C D : Spine.BoundContext) τ q,
  CloseCompatible name d C D → InWindow S K C τ q →
  InWindow S K D τ (closeAt name d q)

/- Moving checked free-name closing past the actual numerical singleton
substitution. `cutoff` counts the residual inner binders while `outer`
is the closing depth at the supplied argument. -/
def ClosingBetaCommutes : Prop := ∀ name outer cutoff (q a : NTerm),
  closeAt name (outer+cutoff) (substitute (.cons a .nil) cutoff q) =
  substitute (.cons (closeAt name outer a) .nil) cutoff (closeAt name (outer+cutoff+1) q)

def ClosingRaw : Prop := ∀ S K name d q r,
  RawStep S K q r → RawStep S K (closeAt name d q) (closeAt name d r)

def ClosingPrimary : Prop := ∀ S K name d (C D : Spine.BoundContext) τ q r,
  CloseCompatible name d C D → Primary S K C τ q r →
  Primary S K D τ (closeAt name d q) (closeAt name d r)

def ClosingTypedTrace : Prop := ∀ S K name d (C D : Spine.BoundContext) τ q r,
  CloseCompatible name d C D →
  ∀ trace : TypedTrace S K C τ q r,
    ∃ out : TypedTrace S K D τ (closeAt name d q) (closeAt name d r),
      vertices out = (vertices trace).map (closeAt name d) ∧ rawLength out = rawLength trace

/-- Agreement with the literal original symbolic closing map at every
realization threshold. It does not perform any beta or eta normalization. -/
def ClosingRealization : Prop := ∀ n (name : Name) (q : Spine.Expr) (Q : NTerm),
  Realizes n q Q → Realizes n (StructuralContext.close name q) (closeAt name 0 Q)

/-- For the actual fresh original opening in Abs, closing the numerical
single-block opening at the same typed name recovers the original body
and all of its labels, not just an equivalent body. -/
def ClosingRecoversAbsBody : Prop := ∀ σ x τ (body : Spine.Expr) n (Q : NTerm),
  Spine.Typed (Spine.EmptyContext.push σ) body τ → freeOccurs (σ,x) body = false →
  Realizes n body Q →
  closeAt (σ,x) 0 (substitute (.cons (.free σ x) .nil) 0 Q) = Q

/-- For the actual named FAbs child of the literal certificate, its body
closes to the actual fresh de Bruijn numeric abstraction body. Original
base, old extras, lower label and original head declaration all remain. -/
def ClosingRecoversFAbsBody : Prop := ∀ f σ τ x (bs es : Spine.Args) n k (Bs Es : NArgs),
  Spine.Typed Spine.EmptyContext (.marked f (.arrow σ τ) bs es) (.arrow σ τ) →
  freeOccurs (σ,x) (.marked f (.arrow σ τ) bs es) = false →
  RealizesArgs n bs Bs → RealizesArgs n es Es →
  closeAt (σ,x) 0 (.numbered f τ k Bs (Es.append (.cons (.free σ x) .nil))) =
    openNumbered f σ τ k Bs Es

def WindowInclusion (K L : List Ty) : Prop := ∀ t, t ∈ K → t ∈ L

/-- Weakening to a containing type window never changes the signature,
typing context, terms, primary permutation or actual raw rules. -/
def EnlargingAdmissibility : Prop := ∀ S K L C τ q,
  WindowInclusion K L → InWindow S K C τ q → InWindow S L C τ q

def EnlargingRaw : Prop := ∀ S K L q r,
  WindowInclusion K L → RawStep S K q r → RawStep S L q r

def EnlargingPrimary : Prop := ∀ S K L C τ q r,
  WindowInclusion K L → Primary S K C τ q r → Primary S L C τ q r

def EnlargingTypedTrace : Prop := ∀ S K L C τ q r,
  WindowInclusion K L →
  ∀ trace : TypedTrace S K C τ q r,
    ∃ out : TypedTrace S L C τ q r,
      vertices out = vertices trace ∧ rawLength out = rawLength trace

end LogicLineages.PersistentMarking.NumberedWindowFrameTargets
