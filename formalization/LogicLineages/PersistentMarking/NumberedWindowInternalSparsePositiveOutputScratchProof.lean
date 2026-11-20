module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputStateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputScratchProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue)
open ID1Completion.InternalListCodec (headCode tailCode)
open ID1Completion.InternalListCodecSupportProof (consDestruction unaryGraph consResult)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePositiveFold (chosenState)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph loopGraph)
open NumberedWindowInternalSparsePositiveOutputTargets
open NumberedWindowInternalSparsePositiveOutputStateProof (stateOfLoop)

attribute [local irreducible] programGraph chosenState

abbrev atState (raw : Program 5) (least : Program 3) (p : Program 1) : Program 4 :=
  .composition p (fun _ : Fin 1 => chosenState raw least)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem evaluateAt (raw : Program 5) (least : Program 3) (p : Program 1)
    (out state ctx ty initial certificate : OTerm α)
    (h : Nonempty (Derivation body Γ (unaryGraph p out state)))
    (returned : Nonempty (Derivation body Γ
      (programGraph (chosenState raw least) state (args4 ctx ty initial certificate)))) :
    Nonempty (Derivation body Γ
      (programGraph (atState raw least p) out (args4 ctx ty initial certificate))) :=
  compositionValue p (fun _ : Fin 1 => chosenState raw least) out
    (args4 ctx ty initial certificate) (Fin.cons state Fin.elim0) h (fun i => by
      obtain rfl := Fin.eq_zero i
      exact returned)

theorem scratchParts (raw : Program 5) (least : Program 3)
    (state ctx ty initial certificate cursor current : OTerm α)
    (loop : Nonempty (Derivation body Γ (loopGraph raw least state certificate ctx ty initial certificate)))
    (pair : Nonempty (Derivation body Γ (scratchGraph state cursor current))) :
    Nonempty (Derivation body Γ
      ((programGraph (atState raw least headCode) cursor (args4 ctx ty initial certificate)) ⊓
        programGraph (atState raw least tailCode) current (args4 ctx ty initial certificate))) := by
  have returned := stateOfLoop raw least state ctx ty initial certificate loop
  obtain ⟨parts⟩ := consDestruction state cursor current pair
  obtain ⟨left⟩ := evaluateAt raw least headCode cursor state ctx ty initial certificate
    ⟨Derivation.conjunctionLeft parts⟩ returned
  obtain ⟨right⟩ := evaluateAt raw least tailCode current state ctx ty initial certificate
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight parts)⟩ returned
  exact ⟨Derivation.conjunctionIntroduction left right⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputScratchProof
