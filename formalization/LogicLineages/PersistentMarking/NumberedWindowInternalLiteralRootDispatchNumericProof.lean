module

public import LogicLineages.PersistentMarking.NumberedWindowRootDispatchProgramTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions
import LogicLineages.PersistentMarking.NumberedWindowRootDispatchStepPrograms
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootDispatchNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch constantZero)
open GorbowVerifierNormalization (normalize)
open InternalAcceptanceCalibrationProof (evalBranch evalNormalize)
open InternalEqualityTestEvaluationProof (vectorOne)
open NumberedWindowRootDispatchAlgorithm (Rules parts check)
open NumberedWindowRootDispatchProgramTargets (PrimitiveRules)
open NumberedWindowRootDispatchStepPrograms (partsPrim PartsInput)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation)
open NumberedWindowInternalSparsePathEnvelope (nodeGood run)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (nodeArity)
open NumberedWindowFieldAlgorithm (unpackNode)

def shapes : List (Nat × Nat) := [(0,1),(1,0),(2,3),(3,0),(4,1),(5,0),(6,0),(7,0)]

def guard (tag arity : Nat) : Program 3 :=
  .composition (nodeGood (literal 1 tag) arity) ![.projection 1]

def route (leaf : Nat → Program 3) : List (Nat × Nat) → Program 3
  | [] => constantZero 3
  | (tag,arity)::rest => branch (normalize (guard tag arity)) (route leaf rest) (leaf tag)

def root (leaf : Nat → Program 3) : Program 3 := route leaf shapes

def ViewMatches (view : Option (Nat × List Nat)) (tag arity : Nat) : Bool :=
  view.any (fun p => p.1 == tag && p.2.length == arity)

def RunRoute (f : Nat → Nat) (view : Option (Nat × List Nat)) : List (Nat × Nat) → Nat
  | [] => 0
  | (tag,arity)::rest => if ViewMatches view tag arity then f tag else RunRoute f view rest

theorem exact_LiteralRootGuard (tag arity q cert r : Nat) :
    evaluate (guard tag arity) (q ::ᵥ cert ::ᵥ r ::ᵥ nil) = 1 ↔
      ∃ fs, unpackNode cert = some (tag,fs) ∧ fs.length = arity := by
  have routed : evaluate (guard tag arity) (q ::ᵥ cert ::ᵥ r ::ᵥ nil) =
      run (nodeGood (literal 1 tag) arity) cert := by
    unfold guard run
    rw [evaluate,vectorOne]
    rfl
  rw [routed]
  exact nodeArity (literal 1 tag) arity cert tag (literalEvaluation 1 tag (cert ::ᵥ nil))

private theorem viewIff (view : Option (Nat × List Nat)) (tag arity : Nat) :
    ViewMatches view tag arity = true ↔ ∃ fs, view = some (tag,fs) ∧ fs.length = arity := by
  cases view with
  | none => simp [ViewMatches]
  | some p =>
    obtain ⟨k,fs⟩ := p
    constructor
    · intro h
      change ((k == tag) && (fs.length == arity)) = true at h
      simp only [Bool.and_eq_true,beq_iff_eq] at h
      exact ⟨fs,by rw [h.1],h.2⟩
    · rintro ⟨values,e,size⟩
      have eq := Prod.mk.inj (Option.some.inj e)
      have len : fs.length = arity := eq.2 ▸ size
      simp [ViewMatches,eq.1,len]

theorem exact_LiteralRouteNumeric (leaf : Nat → Program 3) (q cert r : Nat) (cases : List (Nat × Nat)) :
    evaluate (route leaf cases) (q ::ᵥ cert ::ᵥ r ::ᵥ nil) =
      RunRoute (fun k => evaluate (leaf k) (q ::ᵥ cert ::ᵥ r ::ᵥ nil)) (unpackNode cert) cases := by
  induction cases with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨tag,arity⟩ := p
    rw [route,RunRoute,evalBranch,evalNormalize]
    have guardOk := (exact_LiteralRootGuard tag arity q cert r).trans (viewIff (unpackNode cert) tag arity).symm
    by_cases h : ViewMatches (unpackNode cert) tag arity = true
    · simp [h,guardOk.mpr h]
    · have off : evaluate (guard tag arity) (q ::ᵥ cert ::ᵥ r ::ᵥ nil) ≠ 1 :=
        fun yes => h (guardOk.mp yes)
      simp [h,off,ih]

def LeafFit (rules : Rules) (leaf : Nat → Program 3) : Prop :=
  ∀ tag q cert r fs, unpackNode cert = some (tag,fs) →
    evaluate (leaf tag) (q ::ᵥ cert ::ᵥ r ::ᵥ nil) = (parts rules q r tag fs).toNat

private theorem shapeMeaning (f : Nat → Nat) (rules : Rules) (q r tag : Nat) (fs : List Nat)
    (fit : f tag = (parts rules q r tag fs).toNat) :
    RunRoute f (some (tag,fs)) shapes = (parts rules q r tag fs).toNat := by
  rcases tag with _ | _ | _ | _ | _ | _ | _ | _ | tag <;>
    rcases fs with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,more⟩⟩⟩⟩ <;>
    simp only [shapes,RunRoute,ViewMatches,Option.any,Prod.fst,Prod.snd,List.length_cons,List.length_nil,
      Nat.reduceBEq,Bool.true_and,Bool.false_and,ite_true,ite_false,Bool.decide_coe,
      Nat.succ_ne_zero,parts,Bool.toNat] at * <;> first | exact fit | rfl

/-- The visible eight-way dispatcher is calibrated on every raw input,
including malformed tags, invalid arities and invalid leaf data. -/
theorem exact_LiteralRootNumeric (rules : Rules) (leaf : Nat → Program 3) (fit : LeafFit rules leaf)
    (q cert r : Nat) :
    evaluate (root leaf) (q ::ᵥ cert ::ᵥ r ::ᵥ nil) = (check rules q cert r).toNat := by
  rw [root,exact_LiteralRouteNumeric]
  unfold check
  cases view : unpackNode cert with
  | none => rfl
  | some p =>
    obtain ⟨tag,fs⟩ := p
    exact shapeMeaning _ rules q r tag fs (fit tag q cert r fs view)

private theorem leafPrimitive (rules : Rules) (prim : PrimitiveRules rules) (tag : Nat) :
    Primrec (fun v : List.Vector Nat 3 =>
      (unpackNode v.tail.head).any (fun p => parts rules v.head v.tail.tail.head tag p.2)) := by
  let V := List.Vector Nat 3
  let K := V × (Nat × List Nat)
  have nodes : Primrec unpackNode := Primrec.encode_iff.mp
    ((GorbowPRProgram.Proof.unaryCorrespondence _).mpr NumberedWindowFieldProgramChecks.exact_TaggedNodePrograms.2)
  have hView : Primrec (fun v : V => unpackNode v.tail.head) :=
    nodes.comp (Primrec.vector_head.comp Primrec.vector_tail)
  have a : Primrec (fun p : K => p.1.head) := Primrec.vector_head.comp Primrec.fst
  have dst : Primrec (fun v : V => v.tail.tail.head) := Primrec.vector_head.comp
    (Primrec.vector_tail.comp (Primrec.vector_tail : Primrec (fun v : V => v.tail)))
  have b : Primrec (fun p : K => p.1.tail.tail.head) := dst.comp Primrec.fst
  have fs : Primrec (fun p : K => p.2.2) := Primrec.snd.comp Primrec.snd
  have specialized := (partsPrim prim).comp ((a.pair b).pair ((Primrec.const tag).pair fs))
  exact NumberedWindowSyntaxShapePrograms.anyOption hView specialized.to₂

private theorem boolOutput (b : Bool) : (if b then 1 else 0) = b.toNat := by
  cases b <;> rfl

private theorem pickLeaf (rules : Rules) (prim : PrimitiveRules rules) (tag : Nat) :
    ∃ p : Program 3, ∀ q cert r fs, unpackNode cert = some (tag,fs) →
      evaluate p (q ::ᵥ cert ::ᵥ r ::ᵥ nil) = (parts rules q r tag fs).toNat := by
  have h := leafPrimitive rules prim tag
  obtain ⟨p,h⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 3 _
    ((Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const true)) (Primrec.const 1) (Primrec.const 0)).comp h)
  refine ⟨p,?_⟩
  intro q cert r fs view
  have eq := h (q ::ᵥ cert ::ᵥ r ::ᵥ nil)
  change evaluate p (q ::ᵥ cert ::ᵥ r ::ᵥ nil) =
    (if (unpackNode cert).any (fun a => parts rules q r tag a.2) then 1 else 0) at eq
  rw [view] at eq
  simp only [Option.any] at eq
  rw [eq]
  exact boolOutput (parts rules q r tag fs)

theorem exact_ConcreteLiteralRoot (rules : Rules) (prim : PrimitiveRules rules) :
    ∃ leaf : Nat → Program 3, LeafFit rules leaf ∧
      ∀ q cert r, evaluate (root leaf) (q ::ᵥ cert ::ᵥ r ::ᵥ nil) = (check rules q cert r).toNat := by
  classical
  let leaf : Nat → Program 3 := fun tag => Classical.choose (pickLeaf rules prim tag)
  have fits : LeafFit rules leaf := fun tag => Classical.choose_spec (pickLeaf rules prim tag)
  exact ⟨leaf,fits,exact_LiteralRootNumeric rules leaf fits⟩

#print axioms exact_LiteralRootGuard
#print axioms exact_LiteralRouteNumeric
#print axioms exact_LiteralRootNumeric
#print axioms exact_ConcreteLiteralRoot
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootDispatchNumericProof
