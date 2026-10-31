module
public import Mathlib.Computability.TuringMachine.ToPartrec
@[expose] public section
/-! Executable lists enumerating the actual PartrecToTM2 compiler's support.
No Finset.toList, choice of enumeration, or assumed closure oracle is used.
The input/output convention here is Mathlib's encoded natural-number stacks,
not yet the source paper's raw binary input-tape convention. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerSupport
open Turing Turing.ToPartrec Turing.PartrecToTM2
open Turing.PartrecToTM2.K'

def symbols : List (Option Γ') :=
  [none, some .consₗ, some .cons, some .bit0, some .bit1]

def labelList : Λ' → List Λ'
  | Q@(.move _ _ _ q) => Q :: labelList q
  | Q@(.push _ _ q) => Q :: labelList q
  | Q@(.read f) => Q :: symbols.flatMap (fun s => labelList (f s))
  | Q@(.clear _ _ q) => Q :: labelList q
  | Q@(.copy q) => Q :: labelList q
  | Q@(.succ q) => Q :: unrev q :: labelList q
  | Q@(.pred q₁ q₂) => Q :: (labelList q₁ ++ unrev q₂ :: labelList q₂)
  | Q@(.ret _) => [Q]

def bodyList : Code → Cont' → List Λ'
  | c@Code.zero', k => labelList (trNormal c k)
  | c@Code.succ, k => labelList (trNormal c k)
  | c@Code.tail, k => labelList (trNormal c k)
  | c@(Code.cons f fs), k =>
    labelList (trNormal c k) ++
      (bodyList f (Cont'.cons₁ fs k) ++
        (labelList
            (move₂ (fun _ => false) main aux <|
              move₂ (fun s => s = Γ'.consₗ) stack main <|
                move₂ (fun _ => false) aux stack <| trNormal fs (Cont'.cons₂ k)) ++
          (bodyList fs (Cont'.cons₂ k) ++ labelList (head stack <| Λ'.ret k))))
  | c@(Code.comp f g), k =>
    labelList (trNormal c k) ++
      (bodyList g (Cont'.comp f k) ++ (labelList (trNormal f k) ++ bodyList f k))
  | c@(Code.case f g), k => labelList (trNormal c k) ++ (bodyList f k ++ bodyList g k)
  | c@(Code.fix f), k =>
    labelList (trNormal c k) ++
      (bodyList f (Cont'.fix f k) ++
        (labelList (Λ'.clear natEnd main <| trNormal f (Cont'.fix f k)) ++ [Λ'.ret k]))

def continuationList : Cont' → List Λ'
  | Cont'.cons₁ fs k =>
    labelList
        (move₂ (fun _ => false) main aux <|
          move₂ (fun s => s = Γ'.consₗ) stack main <|
            move₂ (fun _ => false) aux stack <| trNormal fs (Cont'.cons₂ k)) ++
      (bodyList fs (Cont'.cons₂ k) ++ (labelList (head stack <| Λ'.ret k) ++ continuationList k))
  | Cont'.cons₂ k => labelList (head stack <| Λ'.ret k) ++ continuationList k
  | Cont'.comp f k => bodyList f k ++ continuationList k
  | Cont'.fix f k => bodyList (Code.fix f) k ++ continuationList k
  | Cont'.halt => []

def supportList (c : Code) (k : Cont') : List Λ' := bodyList c k ++ continuationList k

end LogicLineages.ComputabilityKnowledge.PredictionCompilerSupport
