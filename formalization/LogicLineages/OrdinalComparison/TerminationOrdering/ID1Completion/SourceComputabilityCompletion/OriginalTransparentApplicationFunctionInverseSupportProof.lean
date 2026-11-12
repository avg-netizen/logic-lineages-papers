module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInverseTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInverseSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsProof
open InternalApplicationStepPeelSupportProof InternalApplicationStepPeelComponentsProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem sameLeft {m : Nat} (p q : Program m) (x : OTerm alpha) (xs : Fin m → OTerm alpha)
 (hs : Nonempty (Derivation body Delta (programGraph (InternalApplicationStepPeel.same p q) (suc z) xs)))
 (hq : Nonempty (Derivation body Delta (programGraph q x xs))) :
 Nonempty (Derivation body Delta (programGraph p x xs)) := by
 apply programCases p xs _
 intro beta j Theta y hj hy
 have hs' := renameInto hs j Theta hj
 have hq' := renameInto hq j Theta hj
 simp only [programRename,sucRelabel,zRelabel] at hs' hq'
 rw [programRename]
 have he := InternalEqualityTestProof.equalityOfAcceptance y (x.relabel j)
   (binaryRecover InternalEqualityTest.equalityTest p q (suc z) y (x.relabel j)
    (fun i => (xs i).relabel j) hs' hy hq')
 exact outputTransport p y (x.relabel j) (fun i => (xs i).relabel j) he hy

theorem sameRight {m : Nat} (p q : Program m) (x : OTerm alpha) (xs : Fin m → OTerm alpha)
 (hs : Nonempty (Derivation body Delta (programGraph (InternalApplicationStepPeel.same p q) (suc z) xs)))
 (hp : Nonempty (Derivation body Delta (programGraph p x xs))) :
 Nonempty (Derivation body Delta (programGraph q x xs)) := by
 apply programCases q xs _
 intro beta j Theta y hj hy
 have hs' := renameInto hs j Theta hj
 have hp' := renameInto hp j Theta hj
 simp only [programRename,sucRelabel,zRelabel] at hs' hp'
 rw [programRename]
 obtain ⟨he⟩ := InternalEqualityTestProof.equalityOfAcceptance (x.relabel j) y
   (binaryRecover InternalEqualityTest.equalityTest p q (suc z) (x.relabel j) y
    (fun i => (xs i).relabel j) hs' hp' hy)
 exact outputTransport q y (x.relabel j) (fun i => (xs i).relabel j) ⟨symm he⟩ hy

def PackedFields (p : Program 1) (state d e fp ap : OTerm alpha) : Formula alpha :=
 graph1 (InternalApplicationStepPeel.outerType p) e state ⊓
 (graph1 (InternalApplicationStepPeel.constructorTag p) positionTerm state ⊓
 (graph1 (InternalApplicationStepPeel.appDomain p) d state ⊓
 (graph1 (InternalApplicationStepPeel.functionPayload p) fp state ⊓
 graph1 (InternalApplicationStepPeel.argumentPayload p) ap state)))
@[simp] theorem packedFieldsRename {beta : Type} (p : Program 1) (state d e fp ap : OTerm alpha) (j : alpha → beta) :
 (PackedFields p state d e fp ap).relabel j = PackedFields p (state.relabel j) (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j) := by
 simp only [PackedFields,conjunctionRename,graph1Rename,positionTerm,GuardedSourceSyntaxProof.numeralRename,sucRelabel,zRelabel]

theorem packedFieldsAt (p : Program 1) (state input d e fp ap : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph1 p input state)))
 (hc : Nonempty (Derivation body Delta (graph4 packedApplication input d e fp ap))) :
 Nonempty (Derivation body Delta (PackedFields p state d e fp ap)) := by
 let children : Program 4 := pairOf (.projection 2) (.projection 3)
 let middle : Program 4 := pairOf (.projection 0) children
 let node : Program 4 := pairOf (two 4) middle
 let qs : Fin 3 → Program 4 := ![children,middle,node]
 let xs : Fin 4 → OTerm alpha := Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))
 apply queryCases qs xs _
 intro beta j ys Theta hj hq
 rw [packedFieldsRename]
 have hp' := renameInto hp j Theta hj
 rw [graph1Rename] at hp'
 have hc' := renameInto hc j Theta hj
 rw [graph4Rename] at hc'
 simp only [xs,consTermRename,emptyRename] at hq
 let xx : Fin 4 → OTerm beta := Fin.cons (d.relabel j) (Fin.cons (e.relabel j) (Fin.cons (fp.relabel j) (Fin.cons (ap.relabel j) Fin.elim0)))
 have hchildren := binaryRecover InternalPairing.pairing (.projection 2) (.projection 3)
   (ys 0) (fp.relabel j) (ap.relabel j) xx (hq 0) (projectionValue 2 xx) (projectionValue 3 xx)
 have hmiddle := binaryRecover InternalPairing.pairing (.projection 0) children
   (ys 1) (d.relabel j) (ys 0) xx (hq 1) (projectionValue 0 xx) (hq 0)
 have hnode := binaryRecover InternalPairing.pairing (two 4) middle
   (ys 2) positionTerm (ys 1) xx (hq 2) (twoValue xx) (hq 1)
 have hinput := binaryRecover InternalPairing.pairing (.projection 1) node
   (input.relabel j) (e.relabel j) (ys 2) xx hc' (projectionValue 1 xx) (hq 2)
 exact InternalApplicationStepPeelComponentsProof.fieldsAtPairs p (state.relabel j) (input.relabel j)
   (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j) (ys 0) (ys 1) (ys 2)
   hp' hchildren hmiddle hnode hinput

/-- Recover all seven literal guard factors, rather than assuming decoded shape. -/
theorem guardParts (state : OTerm alpha)
 (h : Nonempty (Derivation body Delta (graph1 InternalApplicationStepPeel.structuralGuard (suc z) state))) :
 Nonempty (Derivation body Delta
 (graph1 InternalApplicationStepPeel.nonemptyPath (suc z) state ⊓
 (graph1 (InternalApplicationStepPeel.same InternalApplicationStepPeel.pathHead (two 1)) (suc z) state ⊓
 (graph1 (InternalApplicationStepPeel.same (InternalApplicationStepPeel.constructorTag source) (two 1)) (suc z) state ⊓
 (graph1 (InternalApplicationStepPeel.same (InternalApplicationStepPeel.constructorTag target) (two 1)) (suc z) state ⊓
 (graph1 (InternalApplicationStepPeel.same (InternalApplicationStepPeel.outerType source) (InternalApplicationStepPeel.outerType target)) (suc z) state ⊓
 (graph1 (InternalApplicationStepPeel.same (InternalApplicationStepPeel.appDomain source) (InternalApplicationStepPeel.appDomain target)) (suc z) state ⊓
 graph1 (InternalApplicationStepPeel.same (InternalApplicationStepPeel.argumentPayload source) (InternalApplicationStepPeel.argumentPayload target)) (suc z) state))))))) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
 have h1 := conjunctionRecover _ _ xs h
 have h2 := conjunctionRecover _ _ xs (andRight h1)
 have h3 := conjunctionRecover _ _ xs (andRight h2)
 have h4 := conjunctionRecover _ _ xs (andRight h3)
 have h5 := conjunctionRecover _ _ xs (andRight h4)
 have h6 := conjunctionRecover _ _ xs (andRight h5)
 exact andIntro (andLeft h1) (andIntro (andLeft h2) (andIntro (andLeft h3)
   (andIntro (andLeft h4) (andIntro (andLeft h5) (andIntro (andLeft h6) (andRight h6))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInverseSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInverseSupportProof
