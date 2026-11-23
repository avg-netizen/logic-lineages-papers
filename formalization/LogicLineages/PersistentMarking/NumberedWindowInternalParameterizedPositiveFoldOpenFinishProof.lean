module
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenLoopProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputTestProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputStateProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenFinishProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue compositionValue)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalListCodec (headCode tailCode)
open ID1Completion.InternalListCodecSupportProof (consDestruction unaryGraph)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalityOfEqual)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph)
open NumberedWindowInternalSparsePositiveOutputTargets (args4 args5)
open NumberedWindowInternalSparsePositiveOutputWalkProof (succAt succAtValue)
open NumberedWindowInternalSparsePositiveOutputGuardProof (nonemptyCode acceptNonempty)
open NumberedWindowInternalParameterizedPositiveFold
open NumberedWindowInternalParameterizedPositiveFoldOpenLoopProof

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem stateValue (A : Program 4) (state c ty start cert : OTerm α)
    (actual : Nonempty (Derivation body Γ (loopAt A state cert c ty start cert))) :
    Nonempty (Derivation body Γ (programGraph (stateAt A) state (args4 c ty start cert))) := by
  let xs := args4 c ty start cert
  apply compositionValue (iterateAt A) NumberedWindowInternalSparsePositiveOutputStateProof.picks state xs
    ![cert,c,ty,start,cert] actual
  intro i
  exact Fin.cases (projectionValue (3 : Fin 4) xs)
    (Fin.cases (projectionValue (0 : Fin 4) xs) (Fin.cases (projectionValue (1 : Fin 4) xs)
      (Fin.cases (projectionValue (2 : Fin 4) xs) (Fin.cases (projectionValue (3 : Fin 4) xs)
        (fun u => Fin.elim0 u))))) i

private theorem lookup (A : Program 4) (p : Program 1) (out state : OTerm α) (xs : Fin 4 → OTerm α)
    (atState : Nonempty (Derivation body Γ (programGraph (stateAt A) state xs)))
    (read : Nonempty (Derivation body Γ (unaryGraph p out state))) :
    Nonempty (Derivation body Γ (programGraph (.composition p (fun _ : Fin 1 => stateAt A)) out xs)) :=
  compositionValue p (fun _ : Fin 1 => stateAt A) out xs (Fin.cons state Fin.elim0) read
    (fun i => by obtain rfl := Fin.eq_zero i; exact atState)

theorem exact_OpenParameterizedFinish (A : Program 4) (state c ty start cert current : OTerm α)
    (actual : Nonempty (Derivation body Γ (loopAt A state cert c ty start cert)))
    (done : Nonempty (Derivation body Γ (scratchGraph state z current))) :
    Nonempty (Derivation body Γ (programGraph (finishAt A) current (args4 c ty start cert))) := by
  let xs := args4 c ty start cert
  have stateOpen := stateValue A state c ty start cert actual
  obtain ⟨parts⟩ := consDestruction state z current done
  have headOpen := lookup A headCode z state xs stateOpen ⟨Derivation.conjunctionLeft parts⟩
  have tailOpen := lookup A tailCode current state xs stateOpen
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight parts)⟩
  exact zeroBranchIntro (.composition headCode (fun _ : Fin 1 => stateAt A))
    (.composition tailCode (fun _ : Fin 1 => stateAt A)) (constantZero 4) current xs headOpen tailOpen

private theorem walk (A : Program 4) (c ty source cert target current : OTerm α)
    (actual : Nonempty (Derivation body Γ (programGraph (finishAt A) current (args4 c ty (suc source) cert)))) :
    Nonempty (Derivation body Γ (programGraph (walkAt A) current (args5 c ty source cert target))) := by
  let xs := args5 c ty source cert target
  apply compositionValue (finishAt A) NumberedWindowInternalSparsePositiveOutputWalkProof.picks
    current xs (args4 c ty (suc source) cert) actual
  intro i
  exact Fin.cases (projectionValue (0 : Fin 5) xs)
    (Fin.cases (projectionValue (1 : Fin 5) xs)
      (Fin.cases (succAtValue (2 : Fin 5) xs) (Fin.cases (projectionValue (3 : Fin 5) xs)
        (fun u => Fin.elim0 u)))) i

/-- An actual same-body recursor report at the certificate's own fuel, a
terminal scratch and a nonempty certificate suffice for the exact
parameterized positive graph at the held target. No numeric reflection. -/
theorem exact_OpenParameterizedPositiveFromTerminal (A : Program 4)
    (state c ty source cert target : OTerm α)
    (actual : Nonempty (Derivation body Γ (loopAt A state cert c ty (suc source) cert)))
    (done : Nonempty (Derivation body Γ (scratchGraph state z (suc target))))
    (nonemptyCert : Nonempty (Derivation body Γ (eqn cert z).not)) :
    Nonempty (Derivation body Γ (programGraph (positiveAt A) (suc z) (args5 c ty source cert target))) := by
  let xs := args5 c ty source cert target
  let test : Program 5 := .composition equalityTest ![walkAt A,succAt 4]
  have result := walk A c ty source cert target (suc target)
    (exact_OpenParameterizedFinish A state c ty (suc source) cert (suc target) actual done)
  have ok : Nonempty (Derivation body Γ (programGraph test (suc z) xs)) := by
    apply compositionValue equalityTest ![walkAt A,succAt 4] (suc z) xs
      (Fin.cons (suc target) (Fin.cons (suc target) Fin.elim0))
      (equalityOfEqual (suc target) (suc target) ⟨refl (suc target)⟩)
    intro i
    exact Fin.cases result (Fin.cases (succAtValue (4 : Fin 5) xs) (fun u => Fin.elim0 u)) i
  exact conjunctionAccept nonemptyCode test xs (acceptNonempty c ty source cert target nonemptyCert) ok

#print axioms exact_OpenParameterizedFinish
#print axioms exact_OpenParameterizedPositiveFromTerminal
end LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenFinishProof
