module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PositiveGuardTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomSpineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowReductionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PositiveGuardNativeSupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedWindowReduction NumberedWindowEquivalence NumberedLeastCodeRepresentative NumberedQuotientPaths
open NumberedBottomAccessibilitySupportProof NumberedBottomSpine
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def flagValue (measure : Program 1) (value : Nat) : Nat :=
  (Nat.unpair (evaluate measure (List.Vector.ofFn ![value]))).1

def depthValue (measure : Program 1) (value : Nat) : Nat :=
  (Nat.unpair (evaluate measure (List.Vector.ofFn ![value]))).2

/-- Attainment supplies a proper original packed representative even when
the supplied endpoint number was arbitrary. Both original shape invariants
transfer the literal Program contract back to the input packed term. -/
theorem representativeShape (n : Nat) (arity : Fin n → Nat) (bottom measure : Program 1)
    (hc : PositiveGuard.ShapeCalibrated n arity bottom measure)
    (symbols : List (Fin n)) (S Gamma : List Ty) (hS : SubtypeClosed (fun tau => tau ∈ S))
    (q : Packed (Fin n) arity Gamma) (hq : InUniverse symbols S q.2) :
    (evaluate bottom (List.Vector.ofFn ![representativeCode symbols S q]) = 1 ↔
      (bottomView q).isSome = true) ∧
    ((flagValue measure (representativeCode symbols S q) = 1 ↔ BottomSpine q.2) ∧
      depthValue measure (representativeCode symbols S q) = spineDepth q.2) := by
  obtain ⟨r,hr,he⟩ := NumberedLeastCodeRepresentativeProof.representativeAttained
    n arity symbols S hS Gamma q hq
  obtain ⟨hb,hflag,hdepth⟩ := hc Gamma r.1 r.2
  have hview := primaryBottomView hr
  have hspine := NumberedBottomSpineProof.actualPrimarySpineInvariant
    (Fin n) arity symbols S Gamma q r hr
  rw [he]
  constructor
  · simpa only [hview] using hb
  · exact ⟨hflag.trans hspine.1.symm,hdepth.trans hspine.2.symm⟩

theorem quotientEdgeSpine (n : Nat) (arity : Fin n → Nat) (bottom measure : Program 1)
    (hc : PositiveGuard.ShapeCalibrated n arity bottom measure)
    (symbols : List (Fin n)) (S Gamma : List Ty) (hS : SubtypeClosed (fun tau => tau ∈ S))
    (above : Fin n → Fin n → Prop) (x y : Nat)
    (he : QuotientEdge n arity symbols S above Gamma x y)
    (hx : flagValue measure x = 1) :
    flagValue measure y = 1 ∧ depthValue measure y < depthValue measure x := by
  obtain ⟨tau,q,r,hq,hs,hxcode,hycode⟩ := he
  have hr := NumberedWindowReductionProof.stepGood symbols S hS hs hq
  have hqshape := representativeShape n arity bottom measure hc symbols S Gamma hS ⟨tau,q⟩ hq
  have hrshape := representativeShape n arity bottom measure hc symbols S Gamma hS ⟨tau,r⟩ hr
  rw [hxcode] at hqshape
  rw [hycode] at hrshape
  have hbottom := hqshape.2.1.mp hx
  obtain ⟨hnext,hlt⟩ := NumberedBottomSpineProof.actualStepSpineDecrease
    (Fin n) arity symbols S above Gamma tau q r hs hbottom
  refine ⟨hrshape.2.1.mpr hnext,?_⟩
  rw [hqshape.2.2,hrshape.2.2]
  exact hlt

theorem positiveSpine (n : Nat) (arity : Fin n → Nat) (bottom measure : Program 1)
    (hc : PositiveGuard.ShapeCalibrated n arity bottom measure)
    (symbols : List (Fin n)) (S Gamma : List Ty) (hS : SubtypeClosed (fun tau => tau ∈ S))
    (above : Fin n → Fin n → Prop) (x y : Nat)
    (hp : PositivePath (QuotientEdge n arity symbols S above Gamma) x y) :
    flagValue measure x = 1 →
      flagValue measure y = 1 ∧ depthValue measure y < depthValue measure x := by
  induction hp with
  | step he => exact quotientEdgeSpine n arity bottom measure hc symbols S Gamma hS above _ _ he
  | trans h1 h2 ih1 ih2 =>
    intro hx
    obtain ⟨hm,hd1⟩ := ih1 hx
    obtain ⟨hy,hd2⟩ := ih2 hm
    exact ⟨hy,Nat.lt_trans hd2 hd1⟩

theorem bottomShape {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (q : Packed (Fin n) arity Gamma) (h : (bottomView q).isSome = true) :
    BottomSpine q.2 ∧ spineDepth q.2 = 0 := by
  obtain ⟨tau,q⟩ := q
  cases q <;> simp_all [bottomView,BottomSpine,spineDepth]

/-- Literal bottom rejection follows from the SAME native path decrease.
No source-type membership or decoding hypothesis is required of x. -/
theorem positiveNotBottom (n : Nat) (arity : Fin n → Nat) (bottom measure : Program 1)
    (hc : PositiveGuard.ShapeCalibrated n arity bottom measure)
    (symbols : List (Fin n)) (S Gamma : List Ty) (hS : SubtypeClosed (fun tau => tau ∈ S))
    (above : Fin n → Fin n → Prop) (x y : Nat)
    (hp : PositivePath (QuotientEdge n arity symbols S above Gamma) x y) :
    evaluate bottom (List.Vector.ofFn ![x]) ≠ 1 := by
  intro hb
  have hfirst : ∃ z, QuotientEdge n arity symbols S above Gamma x z := by
    induction hp with
    | step he => exact ⟨_,he⟩
    | trans h1 h2 ih1 ih2 => exact ih1
  obtain ⟨z,tau,q,r,hq,hs,hx,hy⟩ := hfirst
  have hqshape := representativeShape n arity bottom measure hc symbols S Gamma hS ⟨tau,q⟩ hq
  rw [hx] at hqshape
  obtain ⟨hqbottom,hdzero⟩ := bottomShape (⟨tau,q⟩ : Packed (Fin n) arity Gamma) (hqshape.1.mp hb)
  have hflag := hqshape.2.1.mpr hqbottom
  have hlt := (positiveSpine n arity bottom measure hc symbols S Gamma hS above x y hp hflag).2
  rw [hqshape.2.2,hdzero] at hlt
  exact Nat.not_lt_zero _ hlt

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PositiveGuardNativeSupportProof
