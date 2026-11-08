module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumeralEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchInvariantProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalCanonicalFixedWindowVertexDispatch InternalApplicationCertificateConstructors
open InternalCanonicalFixedWindowVertexDispatchSupportProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionEqualityProof InternalRecursionClosureLogicProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSupportProof SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalTagArithmeticSyntaxProof (z suc eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem closedFunctionTypedRecover (data : Data) (sigma tau : Ty) (xs : Fin 5 → OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph (closedFunctionTyped data sigma tau) (suc z) xs))) :
    Nonempty (Derivation body Gamma
      (InternalCanonicalQuotientEdgeSelection.typedAccepted data (xs 4)
        (numeral (typeNumber (.arrow sigma tau))))) :=
  binaryRecover (typedChecker data) (.projection 4)
    (constant 5 (typeNumber (.arrow sigma tau))) (suc z) (xs 4)
    (numeral (typeNumber (.arrow sigma tau))) xs h
    (projectionValue 4 xs) (constantValue 5 (typeNumber (.arrow sigma tau)) xs)

theorem closedFunctionTypedAccept (data : Data) (sigma tau : Ty) (xs : Fin 5 → OTerm α)
    (h : Nonempty (Derivation body Gamma
      (InternalCanonicalQuotientEdgeSelection.typedAccepted data (xs 4)
        (numeral (typeNumber (.arrow sigma tau)))))) :
    Nonempty (Derivation body Gamma
      (programGraph (closedFunctionTyped data sigma tau) (suc z) xs)) :=
  binaryValue (typedChecker data) (.projection 4)
    (constant 5 (typeNumber (.arrow sigma tau))) (suc z) (xs 4)
    (numeral (typeNumber (.arrow sigma tau))) xs h
    (projectionValue 4 xs) (constantValue 5 (typeNumber (.arrow sigma tau)) xs)

theorem closedArgumentTypedRecover (data : Data) (sigma : Ty) (xs : Fin 5 → OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph (closedArgumentTyped data sigma) (suc z) xs))) :
    Nonempty (Derivation body Gamma
      (InternalCanonicalQuotientEdgeSelection.typedAccepted data (xs 3)
        (numeral (typeNumber sigma)))) :=
  binaryRecover (typedChecker data) (.projection 3) (constant 5 (typeNumber sigma))
    (suc z) (xs 3) (numeral (typeNumber sigma)) xs h
    (projectionValue 3 xs) (constantValue 5 (typeNumber sigma) xs)

theorem closedArgumentTypedAccept (data : Data) (sigma : Ty) (xs : Fin 5 → OTerm α)
    (h : Nonempty (Derivation body Gamma
      (InternalCanonicalQuotientEdgeSelection.typedAccepted data (xs 3)
        (numeral (typeNumber sigma))))) :
    Nonempty (Derivation body Gamma
      (programGraph (closedArgumentTyped data sigma) (suc z) xs)) :=
  binaryValue (typedChecker data) (.projection 3) (constant 5 (typeNumber sigma))
    (suc z) (xs 3) (numeral (typeNumber sigma)) xs h
    (projectionValue 3 xs) (constantValue 5 (typeNumber sigma) xs)

theorem invariantRecover (window : Nat) (data : Data) (sigma tau : Ty)
    (context domain codomain argument value : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (invariantAccepted window data sigma tau context domain codomain argument value))) :
    Nonempty (Derivation body Gamma
      (invariantFactors window data sigma tau context domain codomain argument value)) := by
  let xs := InternalApplicationPathMap.vertexArguments context domain codomain argument value
  have h0 := conjunctionRecover _ _ xs h
  have h1 := conjunctionRecover _ _ xs (andRight h0)
  have h2 := conjunctionRecover _ _ xs (andRight h1)
  have h3 := conjunctionRecover _ _ xs (andRight h2)
  exact andIntro (coordinateEqualityRecover 5 0 window xs (andLeft h0))
    (andIntro (coordinateEqualityRecover 5 1 (typeNumber sigma) xs (andLeft h1))
      (andIntro (coordinateEqualityRecover 5 2 (typeNumber tau) xs (andLeft h2))
        (andIntro (closedFunctionTypedRecover data sigma tau xs (andLeft h3))
          (closedArgumentTypedRecover data sigma xs (andRight h3)))))

theorem invariantAccept (window : Nat) (data : Data) (sigma tau : Ty)
    (context domain codomain argument value : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (invariantFactors window data sigma tau context domain codomain argument value))) :
    Nonempty (Derivation body Gamma
      (invariantAccepted window data sigma tau context domain codomain argument value)) := by
  let xs := InternalApplicationPathMap.vertexArguments context domain codomain argument value
  exact conjunctionAccept _ _ xs
    (coordinateEqualityAccept 5 0 window xs (andLeft h))
    (conjunctionAccept _ _ xs
      (coordinateEqualityAccept 5 1 (typeNumber sigma) xs (andLeft (andRight h)))
      (conjunctionAccept _ _ xs
        (coordinateEqualityAccept 5 2 (typeNumber tau) xs (andLeft (andRight (andRight h))))
        (conjunctionAccept _ _ xs
          (closedFunctionTypedAccept data sigma tau xs (andLeft (andRight (andRight (andRight h)))))
          (closedArgumentTypedAccept data sigma xs (andRight (andRight (andRight (andRight h))))))))

theorem equalReverse (s t : OTerm α)
    (h : Nonempty (Derivation body Gamma (equal s t))) :
    Nonempty (Derivation body Gamma (equal t s)) := by
  simp only [equalEqn] at h ⊢
  obtain ⟨h⟩ := h
  exact ⟨symm h⟩

theorem equalReflexive (s : OTerm α) :
    Nonempty (Derivation body Gamma (equal s s)) := by
  rw [equalEqn]
  exact ⟨refl s⟩

/-- Only input equality substitution for the actual original arithmetic graph. -/
theorem binaryInputsTransport (p : Program 2) (out x y otherX otherY : OTerm α)
    (hx : Nonempty (Derivation body Gamma (equal x otherX)))
    (hy : Nonempty (Derivation body Gamma (equal y otherY)))
    (h : Nonempty (Derivation body Gamma (graph2 p out x y))) :
    Nonempty (Derivation body Gamma (graph2 p out otherX otherY)) := by
  apply graphInputTransport body α 2 Gamma (OrdinaryArithmetic.graphFormula p) out
    (Fin.cons x (Fin.cons y Fin.elim0)) (Fin.cons otherX (Fin.cons otherY Fin.elim0)) _ h
  intro i
  exact Fin.cases hx (Fin.cases hy (fun j => Fin.elim0 j)) i

/-- Closed original type-code computation only; there is no symbolic reflection. -/
theorem arrowNumeral (sigma tau : Ty) :
    Nonempty (Derivation body Gamma
      (graph2 InternalListCodec.consCode (numeral (typeNumber (.arrow sigma tau)))
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)))) := by
  have ha : evaluate InternalListCodec.consCode
      (List.Vector.ofFn ![typeNumber sigma,typeNumber tau]) = typeNumber (.arrow sigma tau) :=
    InternalListCodecEvaluationProof.consEvaluation (typeNumber sigma) (typeNumber tau)
  have hv : (fun i => (numeral ((List.Vector.ofFn ![typeNumber sigma,typeNumber tau]).get i) : OTerm α)) =
      Fin.cons (numeral (typeNumber sigma)) (Fin.cons (numeral (typeNumber tau)) Fin.elim0) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)) i
  obtain ⟨d⟩ := InternalNumeralEvaluationProof.actualOriginalNumeralEvaluation
    body 2 InternalListCodec.consCode (List.Vector.ofFn ![typeNumber sigma,typeNumber tau]) α
  rw [ha,hv] at d
  exact ⟨weakenClosed d Gamma⟩

theorem invariantActivation (window : Nat) (data : Data) (sigma tau : Ty)
    (context domain codomain argument value : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (invariantAccepted window data sigma tau context domain codomain argument value))) :
    Nonempty (Derivation body Gamma
      (activationAccepted window data context domain codomain argument value)) := by
  have hf := invariantRecover window data sigma tau context domain codomain argument value h
  have hd := equalReverse domain (numeral (typeNumber sigma)) (andLeft (andRight hf))
  have he := equalReverse codomain (numeral (typeNumber tau)) (andLeft (andRight (andRight hf)))
  have har := binaryInputsTransport InternalListCodec.consCode
    (numeral (typeNumber (.arrow sigma tau)))
    (numeral (typeNumber sigma)) (numeral (typeNumber tau)) domain codomain hd he
    (arrowNumeral sigma tau)
  have ha := binaryInputsTransport (typedChecker data) (suc z) argument
    (numeral (typeNumber sigma)) argument domain (equalReflexive argument) hd
    (andRight (andRight (andRight (andRight hf))))
  exact activationAccept window data context domain codomain argument value
    (numeral (typeNumber (.arrow sigma tau))) har
    (andIntro (andLeft hf) (andIntro (andLeft (andRight (andRight (andRight hf)))) ha))

/-- The four path parameters never move. The only transported factor is
canonical typedness of the function value, through the SAME selected Edge. -/
theorem invariantPreserve (window : Nat) (data : Data) (sigma tau : Ty)
    (context domain codomain argument x y certificate : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (invariantAccepted window data sigma tau context domain codomain argument x)))
    (hedge : Nonempty (Derivation body Gamma
      (InternalCanonicalQuotientEdgeSelection.edgeAccepted data x y certificate))) :
    Nonempty (Derivation body Gamma
      (invariantAccepted window data sigma tau context domain codomain argument y)) := by
  have hf := invariantRecover window data sigma tau context domain codomain argument x h
  have hx := andLeft (andRight (andRight (andRight hf)))
  obtain ⟨hp⟩ := andIntro hx hedge
  obtain ⟨hl⟩ := InternalCanonicalQuotientEdgeSelectionProof.actualOriginalCanonicalEdgeTypedPropagation
    body data α Gamma x y certificate (numeral (typeNumber (.arrow sigma tau)))
  have hy := (⟨Derivation.implicationElimination hl hp⟩ : Nonempty (Derivation body Gamma
    (InternalCanonicalQuotientEdgeSelection.typedAccepted data y
      (numeral (typeNumber (.arrow sigma tau))))))
  exact invariantAccept window data sigma tau context domain codomain argument y
    (andIntro (andLeft hf)
      (andIntro (andLeft (andRight hf))
        (andIntro (andLeft (andRight (andRight hf)))
          (andIntro hy (andRight (andRight (andRight (andRight hf))))))))

theorem actualInternalCanonicalFixedWindowInvariantFactors :
    InternalCanonicalFixedWindowVertexDispatchTargets.ActualInternalCanonicalFixedWindowInvariantFactors := by
  intro window data sigma tau body α Delta context domain codomain argument value
  let a := invariantAccepted window data sigma tau context domain codomain argument value
  let f := invariantFactors window data sigma tau context domain codomain argument value
  obtain ⟨hf⟩ := invariantRecover (body := body) (Gamma := a :: Delta)
    window data sigma tau context domain codomain argument value
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := invariantAccept (body := body) (Gamma := f :: Delta)
    window data sigma tau context domain codomain argument value
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

theorem actualInternalCanonicalFixedWindowInvariantActivation :
    InternalCanonicalFixedWindowVertexDispatchTargets.ActualInternalCanonicalFixedWindowInvariantActivation := by
  intro window data sigma tau body α Delta context domain codomain argument value
  let a := invariantAccepted window data sigma tau context domain codomain argument value
  obtain ⟨h⟩ := invariantActivation (body := body) (Gamma := a :: Delta)
    window data sigma tau context domain codomain argument value
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualInternalCanonicalFixedWindowInvariantPreservation :
    InternalCanonicalFixedWindowVertexDispatchTargets.ActualInternalCanonicalFixedWindowInvariantPreservation := by
  intro window data body sigma tau α ps x y certificate
  let premise := InternalApplicationPathLift.invariantAt (invariant window data sigma tau) ps x ⊓
    InternalPathChecker.edgeGraph (InternalCanonicalQuotientEdgeSelection.edgeChecker data) x y certificate
  have hp : Nonempty (Derivation body [premise] premise) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := invariantPreserve (body := body) (Gamma := [premise]) window data sigma tau
    (ps 0) (ps 1) (ps 2) (ps 3) x y certificate (andLeft hp) (andRight hp)
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchInvariantProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchInvariantProof
