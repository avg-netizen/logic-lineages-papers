module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.GuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledStructuralFields.LambdaProof
public import Mathlib.Tactic.FinCases
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.LayerProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
/-- Actual slot17/18 overrides moved into unused structural supplier positions.
This is an AST identity, not a calibrated filler hypothesis. -/
def filled (n : Nat) (arity : Fin n → Nat) (V : Program 3) (i : Fin 19) : Program 3 :=
  if i = 17 then HeadResultFields.result V false else
  if i = 18 then HeadResultFields.result V true else
    HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun j => Fin.elim0 j)) V i

theorem fieldsIdentity (n : Nat) (arity : Fin n → Nat) (V : Program 3) :
    ResultStructuralFields.fields
      (HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun j => Fin.elim0 j)) V) V =
    StructuralExchangeFields.fields (filled n arity V) V := by
  funext i
  fin_cases i
  · change ResultStructuralFields.fields
      (HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun k => Fin.elim0 k)) V) V (0 : Fin 19) =
        StructuralExchangeFields.fields (filled n arity V) V (0 : Fin 19)
    simp only [ResultStructuralFields.fields, StructuralExchangeFields.fields, filled,
      if_pos (show (0: Fin 19) = 0 from rfl),
      if_neg (by decide : (0: Fin 19) ≠ 1),
      if_neg (by decide : (0: Fin 19) ≠ 2),
      if_neg (by decide : (0: Fin 19) ≠ 3),
      if_neg (by decide : (0: Fin 19) ≠ 4),
      if_neg (by decide : (0: Fin 19) ≠ 5),
      if_neg (by decide : (0: Fin 19) ≠ 6),
      if_neg (by decide : (0: Fin 19) ≠ 7),
      if_neg (by decide : (0: Fin 19) ≠ 8),
      if_neg (by decide : (0: Fin 19) ≠ 9),
      if_neg (by decide : (0: Fin 19) ≠ 10),
      if_neg (by decide : (0: Fin 19) ≠ 11),
      if_neg (by decide : (0: Fin 19) ≠ 12),
      if_neg (by decide : (0: Fin 19) ≠ 13),
      if_neg (by decide : (0: Fin 19) ≠ 17),
      if_neg (by decide : (0: Fin 19) ≠ 18)]
  · change ResultStructuralFields.fields
      (HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun k => Fin.elim0 k)) V) V (1 : Fin 19) =
        StructuralExchangeFields.fields (filled n arity V) V (1 : Fin 19)
    simp only [ResultStructuralFields.fields, StructuralExchangeFields.fields, filled,
      if_neg (by decide : (1: Fin 19) ≠ 0),
      if_pos (show (1: Fin 19) = 1 from rfl),
      if_neg (by decide : (1: Fin 19) ≠ 2),
      if_neg (by decide : (1: Fin 19) ≠ 3),
      if_neg (by decide : (1: Fin 19) ≠ 4),
      if_neg (by decide : (1: Fin 19) ≠ 5),
      if_neg (by decide : (1: Fin 19) ≠ 6),
      if_neg (by decide : (1: Fin 19) ≠ 7),
      if_neg (by decide : (1: Fin 19) ≠ 8),
      if_neg (by decide : (1: Fin 19) ≠ 9),
      if_neg (by decide : (1: Fin 19) ≠ 10),
      if_neg (by decide : (1: Fin 19) ≠ 11),
      if_neg (by decide : (1: Fin 19) ≠ 12),
      if_neg (by decide : (1: Fin 19) ≠ 13),
      if_neg (by decide : (1: Fin 19) ≠ 17),
      if_neg (by decide : (1: Fin 19) ≠ 18)]
  · change ResultStructuralFields.fields
      (HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun k => Fin.elim0 k)) V) V (2 : Fin 19) =
        StructuralExchangeFields.fields (filled n arity V) V (2 : Fin 19)
    simp only [ResultStructuralFields.fields, StructuralExchangeFields.fields, filled,
      if_neg (by decide : (2: Fin 19) ≠ 0),
      if_neg (by decide : (2: Fin 19) ≠ 1),
      if_pos (show (2: Fin 19) = 2 from rfl),
      if_neg (by decide : (2: Fin 19) ≠ 3),
      if_neg (by decide : (2: Fin 19) ≠ 4),
      if_neg (by decide : (2: Fin 19) ≠ 5),
      if_neg (by decide : (2: Fin 19) ≠ 6),
      if_neg (by decide : (2: Fin 19) ≠ 7),
      if_neg (by decide : (2: Fin 19) ≠ 8),
      if_neg (by decide : (2: Fin 19) ≠ 9),
      if_neg (by decide : (2: Fin 19) ≠ 10),
      if_neg (by decide : (2: Fin 19) ≠ 11),
      if_neg (by decide : (2: Fin 19) ≠ 12),
      if_neg (by decide : (2: Fin 19) ≠ 13),
      if_neg (by decide : (2: Fin 19) ≠ 17),
      if_neg (by decide : (2: Fin 19) ≠ 18)]
  · change ResultStructuralFields.fields
      (HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun k => Fin.elim0 k)) V) V (3 : Fin 19) =
        StructuralExchangeFields.fields (filled n arity V) V (3 : Fin 19)
    simp only [ResultStructuralFields.fields, StructuralExchangeFields.fields, filled,
      if_neg (by decide : (3: Fin 19) ≠ 0),
      if_neg (by decide : (3: Fin 19) ≠ 1),
      if_neg (by decide : (3: Fin 19) ≠ 2),
      if_pos (show (3: Fin 19) = 3 from rfl),
      if_neg (by decide : (3: Fin 19) ≠ 4),
      if_neg (by decide : (3: Fin 19) ≠ 5),
      if_neg (by decide : (3: Fin 19) ≠ 6),
      if_neg (by decide : (3: Fin 19) ≠ 7),
      if_neg (by decide : (3: Fin 19) ≠ 8),
      if_neg (by decide : (3: Fin 19) ≠ 9),
      if_neg (by decide : (3: Fin 19) ≠ 10),
      if_neg (by decide : (3: Fin 19) ≠ 11),
      if_neg (by decide : (3: Fin 19) ≠ 12),
      if_neg (by decide : (3: Fin 19) ≠ 13),
      if_neg (by decide : (3: Fin 19) ≠ 17),
      if_neg (by decide : (3: Fin 19) ≠ 18)]
  · change ResultStructuralFields.fields
      (HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun k => Fin.elim0 k)) V) V (4 : Fin 19) =
        StructuralExchangeFields.fields (filled n arity V) V (4 : Fin 19)
    simp only [ResultStructuralFields.fields, StructuralExchangeFields.fields, filled,
      if_neg (by decide : (4: Fin 19) ≠ 0),
      if_neg (by decide : (4: Fin 19) ≠ 1),
      if_neg (by decide : (4: Fin 19) ≠ 2),
      if_neg (by decide : (4: Fin 19) ≠ 3),
      if_pos (show (4: Fin 19) = 4 from rfl),
      if_neg (by decide : (4: Fin 19) ≠ 5),
      if_neg (by decide : (4: Fin 19) ≠ 6),
      if_neg (by decide : (4: Fin 19) ≠ 7),
      if_neg (by decide : (4: Fin 19) ≠ 8),
      if_neg (by decide : (4: Fin 19) ≠ 9),
      if_neg (by decide : (4: Fin 19) ≠ 10),
      if_neg (by decide : (4: Fin 19) ≠ 11),
      if_neg (by decide : (4: Fin 19) ≠ 12),
      if_neg (by decide : (4: Fin 19) ≠ 13),
      if_neg (by decide : (4: Fin 19) ≠ 17),
      if_neg (by decide : (4: Fin 19) ≠ 18)]
  · change ResultStructuralFields.fields
      (HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun k => Fin.elim0 k)) V) V (5 : Fin 19) =
        StructuralExchangeFields.fields (filled n arity V) V (5 : Fin 19)
    simp only [ResultStructuralFields.fields, StructuralExchangeFields.fields, filled,
      if_neg (by decide : (5: Fin 19) ≠ 0),
      if_neg (by decide : (5: Fin 19) ≠ 1),
      if_neg (by decide : (5: Fin 19) ≠ 2),
      if_neg (by decide : (5: Fin 19) ≠ 3),
      if_neg (by decide : (5: Fin 19) ≠ 4),
      if_pos (show (5: Fin 19) = 5 from rfl),
      if_neg (by decide : (5: Fin 19) ≠ 6),
      if_neg (by decide : (5: Fin 19) ≠ 7),
      if_neg (by decide : (5: Fin 19) ≠ 8),
      if_neg (by decide : (5: Fin 19) ≠ 9),
      if_neg (by decide : (5: Fin 19) ≠ 10),
      if_neg (by decide : (5: Fin 19) ≠ 11),
      if_neg (by decide : (5: Fin 19) ≠ 12),
      if_neg (by decide : (5: Fin 19) ≠ 13),
      if_neg (by decide : (5: Fin 19) ≠ 17),
      if_neg (by decide : (5: Fin 19) ≠ 18)]
  · change ResultStructuralFields.fields
      (HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun k => Fin.elim0 k)) V) V (6 : Fin 19) =
        StructuralExchangeFields.fields (filled n arity V) V (6 : Fin 19)
    simp only [ResultStructuralFields.fields, StructuralExchangeFields.fields, filled,
      if_neg (by decide : (6: Fin 19) ≠ 0),
      if_neg (by decide : (6: Fin 19) ≠ 1),
      if_neg (by decide : (6: Fin 19) ≠ 2),
      if_neg (by decide : (6: Fin 19) ≠ 3),
      if_neg (by decide : (6: Fin 19) ≠ 4),
      if_neg (by decide : (6: Fin 19) ≠ 5),
      if_pos (show (6: Fin 19) = 6 from rfl),
      if_neg (by decide : (6: Fin 19) ≠ 7),
      if_neg (by decide : (6: Fin 19) ≠ 8),
      if_neg (by decide : (6: Fin 19) ≠ 9),
      if_neg (by decide : (6: Fin 19) ≠ 10),
      if_neg (by decide : (6: Fin 19) ≠ 11),
      if_neg (by decide : (6: Fin 19) ≠ 12),
      if_neg (by decide : (6: Fin 19) ≠ 13),
      if_neg (by decide : (6: Fin 19) ≠ 17),
      if_neg (by decide : (6: Fin 19) ≠ 18)]
  · change ResultStructuralFields.fields
      (HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun k => Fin.elim0 k)) V) V (7 : Fin 19) =
        StructuralExchangeFields.fields (filled n arity V) V (7 : Fin 19)
    simp only [ResultStructuralFields.fields, StructuralExchangeFields.fields, filled,
      if_neg (by decide : (7: Fin 19) ≠ 0),
      if_neg (by decide : (7: Fin 19) ≠ 1),
      if_neg (by decide : (7: Fin 19) ≠ 2),
      if_neg (by decide : (7: Fin 19) ≠ 3),
      if_neg (by decide : (7: Fin 19) ≠ 4),
      if_neg (by decide : (7: Fin 19) ≠ 5),
      if_neg (by decide : (7: Fin 19) ≠ 6),
      if_pos (show (7: Fin 19) = 7 from rfl),
      if_neg (by decide : (7: Fin 19) ≠ 8),
      if_neg (by decide : (7: Fin 19) ≠ 9),
      if_neg (by decide : (7: Fin 19) ≠ 10),
      if_neg (by decide : (7: Fin 19) ≠ 11),
      if_neg (by decide : (7: Fin 19) ≠ 12),
      if_neg (by decide : (7: Fin 19) ≠ 13),
      if_neg (by decide : (7: Fin 19) ≠ 17),
      if_neg (by decide : (7: Fin 19) ≠ 18)]
  · change ResultStructuralFields.fields
      (HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun k => Fin.elim0 k)) V) V (8 : Fin 19) =
        StructuralExchangeFields.fields (filled n arity V) V (8 : Fin 19)
    simp only [ResultStructuralFields.fields, StructuralExchangeFields.fields, filled,
      if_neg (by decide : (8: Fin 19) ≠ 0),
      if_neg (by decide : (8: Fin 19) ≠ 1),
      if_neg (by decide : (8: Fin 19) ≠ 2),
      if_neg (by decide : (8: Fin 19) ≠ 3),
      if_neg (by decide : (8: Fin 19) ≠ 4),
      if_neg (by decide : (8: Fin 19) ≠ 5),
      if_neg (by decide : (8: Fin 19) ≠ 6),
      if_neg (by decide : (8: Fin 19) ≠ 7),
      if_pos (show (8: Fin 19) = 8 from rfl),
      if_neg (by decide : (8: Fin 19) ≠ 9),
      if_neg (by decide : (8: Fin 19) ≠ 10),
      if_neg (by decide : (8: Fin 19) ≠ 11),
      if_neg (by decide : (8: Fin 19) ≠ 12),
      if_neg (by decide : (8: Fin 19) ≠ 13),
      if_neg (by decide : (8: Fin 19) ≠ 17),
      if_neg (by decide : (8: Fin 19) ≠ 18)]
  · change ResultStructuralFields.fields
      (HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun k => Fin.elim0 k)) V) V (9 : Fin 19) =
        StructuralExchangeFields.fields (filled n arity V) V (9 : Fin 19)
    simp only [ResultStructuralFields.fields, StructuralExchangeFields.fields, filled,
      if_neg (by decide : (9: Fin 19) ≠ 0),
      if_neg (by decide : (9: Fin 19) ≠ 1),
      if_neg (by decide : (9: Fin 19) ≠ 2),
      if_neg (by decide : (9: Fin 19) ≠ 3),
      if_neg (by decide : (9: Fin 19) ≠ 4),
      if_neg (by decide : (9: Fin 19) ≠ 5),
      if_neg (by decide : (9: Fin 19) ≠ 6),
      if_neg (by decide : (9: Fin 19) ≠ 7),
      if_neg (by decide : (9: Fin 19) ≠ 8),
      if_pos (show (9: Fin 19) = 9 from rfl),
      if_neg (by decide : (9: Fin 19) ≠ 10),
      if_neg (by decide : (9: Fin 19) ≠ 11),
      if_neg (by decide : (9: Fin 19) ≠ 12),
      if_neg (by decide : (9: Fin 19) ≠ 13),
      if_neg (by decide : (9: Fin 19) ≠ 17),
      if_neg (by decide : (9: Fin 19) ≠ 18)]
  · change ResultStructuralFields.fields
      (HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun k => Fin.elim0 k)) V) V (10 : Fin 19) =
        StructuralExchangeFields.fields (filled n arity V) V (10 : Fin 19)
    simp only [ResultStructuralFields.fields, StructuralExchangeFields.fields, filled,
      if_neg (by decide : (10: Fin 19) ≠ 0),
      if_neg (by decide : (10: Fin 19) ≠ 1),
      if_neg (by decide : (10: Fin 19) ≠ 2),
      if_neg (by decide : (10: Fin 19) ≠ 3),
      if_neg (by decide : (10: Fin 19) ≠ 4),
      if_neg (by decide : (10: Fin 19) ≠ 5),
      if_neg (by decide : (10: Fin 19) ≠ 6),
      if_neg (by decide : (10: Fin 19) ≠ 7),
      if_neg (by decide : (10: Fin 19) ≠ 8),
      if_neg (by decide : (10: Fin 19) ≠ 9),
      if_pos (show (10: Fin 19) = 10 from rfl),
      if_neg (by decide : (10: Fin 19) ≠ 11),
      if_neg (by decide : (10: Fin 19) ≠ 12),
      if_neg (by decide : (10: Fin 19) ≠ 13),
      if_neg (by decide : (10: Fin 19) ≠ 17),
      if_neg (by decide : (10: Fin 19) ≠ 18)]
  · change ResultStructuralFields.fields
      (HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun k => Fin.elim0 k)) V) V (11 : Fin 19) =
        StructuralExchangeFields.fields (filled n arity V) V (11 : Fin 19)
    simp only [ResultStructuralFields.fields, StructuralExchangeFields.fields, filled,
      if_neg (by decide : (11: Fin 19) ≠ 0),
      if_neg (by decide : (11: Fin 19) ≠ 1),
      if_neg (by decide : (11: Fin 19) ≠ 2),
      if_neg (by decide : (11: Fin 19) ≠ 3),
      if_neg (by decide : (11: Fin 19) ≠ 4),
      if_neg (by decide : (11: Fin 19) ≠ 5),
      if_neg (by decide : (11: Fin 19) ≠ 6),
      if_neg (by decide : (11: Fin 19) ≠ 7),
      if_neg (by decide : (11: Fin 19) ≠ 8),
      if_neg (by decide : (11: Fin 19) ≠ 9),
      if_neg (by decide : (11: Fin 19) ≠ 10),
      if_pos (show (11: Fin 19) = 11 from rfl),
      if_neg (by decide : (11: Fin 19) ≠ 12),
      if_neg (by decide : (11: Fin 19) ≠ 13),
      if_neg (by decide : (11: Fin 19) ≠ 17),
      if_neg (by decide : (11: Fin 19) ≠ 18)]
  · change ResultStructuralFields.fields
      (HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun k => Fin.elim0 k)) V) V (12 : Fin 19) =
        StructuralExchangeFields.fields (filled n arity V) V (12 : Fin 19)
    simp only [ResultStructuralFields.fields, StructuralExchangeFields.fields, filled,
      if_neg (by decide : (12: Fin 19) ≠ 0),
      if_neg (by decide : (12: Fin 19) ≠ 1),
      if_neg (by decide : (12: Fin 19) ≠ 2),
      if_neg (by decide : (12: Fin 19) ≠ 3),
      if_neg (by decide : (12: Fin 19) ≠ 4),
      if_neg (by decide : (12: Fin 19) ≠ 5),
      if_neg (by decide : (12: Fin 19) ≠ 6),
      if_neg (by decide : (12: Fin 19) ≠ 7),
      if_neg (by decide : (12: Fin 19) ≠ 8),
      if_neg (by decide : (12: Fin 19) ≠ 9),
      if_neg (by decide : (12: Fin 19) ≠ 10),
      if_neg (by decide : (12: Fin 19) ≠ 11),
      if_pos (show (12: Fin 19) = 12 from rfl),
      if_neg (by decide : (12: Fin 19) ≠ 13),
      if_neg (by decide : (12: Fin 19) ≠ 17),
      if_neg (by decide : (12: Fin 19) ≠ 18)]
  · change ResultStructuralFields.fields
      (HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun k => Fin.elim0 k)) V) V (13 : Fin 19) =
        StructuralExchangeFields.fields (filled n arity V) V (13 : Fin 19)
    simp only [ResultStructuralFields.fields, StructuralExchangeFields.fields, filled,
      if_neg (by decide : (13: Fin 19) ≠ 0),
      if_neg (by decide : (13: Fin 19) ≠ 1),
      if_neg (by decide : (13: Fin 19) ≠ 2),
      if_neg (by decide : (13: Fin 19) ≠ 3),
      if_neg (by decide : (13: Fin 19) ≠ 4),
      if_neg (by decide : (13: Fin 19) ≠ 5),
      if_neg (by decide : (13: Fin 19) ≠ 6),
      if_neg (by decide : (13: Fin 19) ≠ 7),
      if_neg (by decide : (13: Fin 19) ≠ 8),
      if_neg (by decide : (13: Fin 19) ≠ 9),
      if_neg (by decide : (13: Fin 19) ≠ 10),
      if_neg (by decide : (13: Fin 19) ≠ 11),
      if_neg (by decide : (13: Fin 19) ≠ 12),
      if_pos (show (13: Fin 19) = 13 from rfl),
      if_neg (by decide : (13: Fin 19) ≠ 17),
      if_neg (by decide : (13: Fin 19) ≠ 18)]
  · change ResultStructuralFields.fields
      (HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun k => Fin.elim0 k)) V) V (14 : Fin 19) =
        StructuralExchangeFields.fields (filled n arity V) V (14 : Fin 19)
    simp only [ResultStructuralFields.fields, StructuralExchangeFields.fields, filled,
      if_neg (by decide : (14: Fin 19) ≠ 0),
      if_neg (by decide : (14: Fin 19) ≠ 1),
      if_neg (by decide : (14: Fin 19) ≠ 2),
      if_neg (by decide : (14: Fin 19) ≠ 3),
      if_neg (by decide : (14: Fin 19) ≠ 4),
      if_neg (by decide : (14: Fin 19) ≠ 5),
      if_neg (by decide : (14: Fin 19) ≠ 6),
      if_neg (by decide : (14: Fin 19) ≠ 7),
      if_neg (by decide : (14: Fin 19) ≠ 8),
      if_neg (by decide : (14: Fin 19) ≠ 9),
      if_neg (by decide : (14: Fin 19) ≠ 10),
      if_neg (by decide : (14: Fin 19) ≠ 11),
      if_neg (by decide : (14: Fin 19) ≠ 12),
      if_neg (by decide : (14: Fin 19) ≠ 13),
      if_neg (by decide : (14: Fin 19) ≠ 17),
      if_neg (by decide : (14: Fin 19) ≠ 18)]
  · change ResultStructuralFields.fields
      (HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun k => Fin.elim0 k)) V) V (15 : Fin 19) =
        StructuralExchangeFields.fields (filled n arity V) V (15 : Fin 19)
    simp only [ResultStructuralFields.fields, StructuralExchangeFields.fields, filled,
      if_neg (by decide : (15: Fin 19) ≠ 0),
      if_neg (by decide : (15: Fin 19) ≠ 1),
      if_neg (by decide : (15: Fin 19) ≠ 2),
      if_neg (by decide : (15: Fin 19) ≠ 3),
      if_neg (by decide : (15: Fin 19) ≠ 4),
      if_neg (by decide : (15: Fin 19) ≠ 5),
      if_neg (by decide : (15: Fin 19) ≠ 6),
      if_neg (by decide : (15: Fin 19) ≠ 7),
      if_neg (by decide : (15: Fin 19) ≠ 8),
      if_neg (by decide : (15: Fin 19) ≠ 9),
      if_neg (by decide : (15: Fin 19) ≠ 10),
      if_neg (by decide : (15: Fin 19) ≠ 11),
      if_neg (by decide : (15: Fin 19) ≠ 12),
      if_neg (by decide : (15: Fin 19) ≠ 13),
      if_neg (by decide : (15: Fin 19) ≠ 17),
      if_neg (by decide : (15: Fin 19) ≠ 18)]
  · change ResultStructuralFields.fields
      (HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun k => Fin.elim0 k)) V) V (16 : Fin 19) =
        StructuralExchangeFields.fields (filled n arity V) V (16 : Fin 19)
    simp only [ResultStructuralFields.fields, StructuralExchangeFields.fields, filled,
      if_neg (by decide : (16: Fin 19) ≠ 0),
      if_neg (by decide : (16: Fin 19) ≠ 1),
      if_neg (by decide : (16: Fin 19) ≠ 2),
      if_neg (by decide : (16: Fin 19) ≠ 3),
      if_neg (by decide : (16: Fin 19) ≠ 4),
      if_neg (by decide : (16: Fin 19) ≠ 5),
      if_neg (by decide : (16: Fin 19) ≠ 6),
      if_neg (by decide : (16: Fin 19) ≠ 7),
      if_neg (by decide : (16: Fin 19) ≠ 8),
      if_neg (by decide : (16: Fin 19) ≠ 9),
      if_neg (by decide : (16: Fin 19) ≠ 10),
      if_neg (by decide : (16: Fin 19) ≠ 11),
      if_neg (by decide : (16: Fin 19) ≠ 12),
      if_neg (by decide : (16: Fin 19) ≠ 13),
      if_neg (by decide : (16: Fin 19) ≠ 17),
      if_neg (by decide : (16: Fin 19) ≠ 18)]
  · change ResultStructuralFields.fields
      (HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun k => Fin.elim0 k)) V) V (17 : Fin 19) =
        StructuralExchangeFields.fields (filled n arity V) V (17 : Fin 19)
    simp only [ResultStructuralFields.fields, StructuralExchangeFields.fields, filled,
      if_neg (by decide : (17: Fin 19) ≠ 0),
      if_neg (by decide : (17: Fin 19) ≠ 1),
      if_neg (by decide : (17: Fin 19) ≠ 2),
      if_neg (by decide : (17: Fin 19) ≠ 3),
      if_neg (by decide : (17: Fin 19) ≠ 4),
      if_neg (by decide : (17: Fin 19) ≠ 5),
      if_neg (by decide : (17: Fin 19) ≠ 6),
      if_neg (by decide : (17: Fin 19) ≠ 7),
      if_neg (by decide : (17: Fin 19) ≠ 8),
      if_neg (by decide : (17: Fin 19) ≠ 9),
      if_neg (by decide : (17: Fin 19) ≠ 10),
      if_neg (by decide : (17: Fin 19) ≠ 11),
      if_neg (by decide : (17: Fin 19) ≠ 12),
      if_neg (by decide : (17: Fin 19) ≠ 13),
      if_pos (show (17: Fin 19) = 17 from rfl),
      if_neg (by decide : (17: Fin 19) ≠ 18)]
  · change ResultStructuralFields.fields
      (HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun k => Fin.elim0 k)) V) V (18 : Fin 19) =
        StructuralExchangeFields.fields (filled n arity V) V (18 : Fin 19)
    simp only [ResultStructuralFields.fields, StructuralExchangeFields.fields, filled,
      if_neg (by decide : (18: Fin 19) ≠ 0),
      if_neg (by decide : (18: Fin 19) ≠ 1),
      if_neg (by decide : (18: Fin 19) ≠ 2),
      if_neg (by decide : (18: Fin 19) ≠ 3),
      if_neg (by decide : (18: Fin 19) ≠ 4),
      if_neg (by decide : (18: Fin 19) ≠ 5),
      if_neg (by decide : (18: Fin 19) ≠ 6),
      if_neg (by decide : (18: Fin 19) ≠ 7),
      if_neg (by decide : (18: Fin 19) ≠ 8),
      if_neg (by decide : (18: Fin 19) ≠ 9),
      if_neg (by decide : (18: Fin 19) ≠ 10),
      if_neg (by decide : (18: Fin 19) ≠ 11),
      if_neg (by decide : (18: Fin 19) ≠ 12),
      if_neg (by decide : (18: Fin 19) ≠ 13),
      if_neg (by decide : (18: Fin 19) ≠ 17),
      if_pos (show (18: Fin 19) = 18 from rfl)]

theorem layerIdentity (n : Nat) (arity : Fin n → Nat) (V : Program 3) :
    ConcreteHeadMoveLayer.layer n arity V = StructuralExchangeFields.layer (filled n arity V) V := by
  unfold ConcreteHeadMoveLayer.layer HeadMoveFields.layer ResultStructuralFields.layer StructuralExchangeFields.layer
  exact congrArg (fun U => TransparentExchangeLayer.optional U V) (fieldsIdentity n arity V)

theorem lambda (n : Nat) (arity : Fin n → Nat) (node code param source target sigma tau q r head tail : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node code param)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hs : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor source sigma q)))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor target tau r)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail))) :
    (Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.layer n arity) (numeral 2) node code param)) ↔
     Nonempty (Derivation body Delta (eqn sigma tau ⊓ eqn head (numeral 1)))) := by
  unfold OriginalDecodedLayerCalibration.layer
  rw [layerIdentity]
  exact InstalledStructuralFields.LambdaProof.internalLambda (filled n arity (OriginalDecodedLayerCalibration.guard n))
    (OriginalDecodedLayerCalibration.guard n) body alpha Delta node code param source target sigma tau q r head tail hg hn hs ht hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.LayerProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.LayerProof
