module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSyntaxBoundsPrimrecTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeViewProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSyntaxBoundsPrimrecSupportProof
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedCodeView
open NumberedSyntaxBoundsPrimrec NumberedHeadCodecPrimrecSupportProof

def children {Symbol : Type} : Code Symbol → List (Code Symbol)
  | .var _ | .bottom _ | .argumentsNil => []
  | .lam _ body | .ordinary _ body => [body]
  | .app _ q a | .argumentsCons _ q a => [q, a]
  | .numbered _ _ _ base _ extras => [base, extras]

def rootBounds {Symbol : Type} : Code Symbol → Nat × Nat
  | .argumentsNil | .argumentsCons _ _ _ => (0, 0)
  | .numbered k _ _ _ _ _ => (1, k)
  | _ => (1, 0)

def viewChildren (n : Nat) : CodeView n → List (Code (Fin n)) :=
  Sum.elim (fun _ : Nat => [])
    (Sum.elim (fun p : Ty × Code (Fin n) => [p.2])
      (Sum.elim (fun p : Ty × Code (Fin n) × Code (Fin n) => [p.2.1, p.2.2])
        (Sum.elim (fun _ : Ty => [])
          (Sum.elim (fun p : HeadCode (Fin n) × Code (Fin n) => [p.2])
            (Sum.elim
              (fun p : Nat × HeadCode (Fin n) × Ty × Code (Fin n) × List Ty × Code (Fin n) =>
                [p.2.2.2.1, p.2.2.2.2.2])
              (Sum.elim (fun _ : Unit => [])
                (fun p : Ty × Code (Fin n) × Code (Fin n) => [p.2.1, p.2.2])))))))

def viewRootBounds (n : Nat) : CodeView n → Nat × Nat :=
  Sum.elim (fun _ : Nat => (1, 0))
    (Sum.elim (fun _ : Ty × Code (Fin n) => (1, 0))
      (Sum.elim (fun _ : Ty × Code (Fin n) × Code (Fin n) => (1, 0))
        (Sum.elim (fun _ : Ty => (1, 0))
          (Sum.elim (fun _ : HeadCode (Fin n) × Code (Fin n) => (1, 0))
            (Sum.elim
              (fun p : Nat × HeadCode (Fin n) × Ty × Code (Fin n) × List Ty × Code (Fin n) =>
                (1, p.1))
              (Sum.elim (fun _ : Unit => (0, 0))
                (fun _ : Ty × Code (Fin n) × Code (Fin n) => (0, 0))))))))

theorem singletonPrimitive {A B : Type} [Primcodable A] [Primcodable B]
    {f : A → B} (hf : Primrec f) : Primrec (fun a => [f a]) :=
  Primrec.list_cons.comp hf (Primrec.const [])

theorem doubletonPrimitive {A B : Type} [Primcodable A] [Primcodable B]
    {f g : A → B} (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => [f a, g a]) :=
  Primrec.list_cons.comp hf (Primrec.list_cons.comp hg (Primrec.const []))

theorem viewChildrenPrimitive (n : Nat) : Primrec (viewChildren n) := by
  unfold viewChildren
  apply sumElim (Primrec.const [])
  apply sumElim (singletonPrimitive Primrec.snd)
  apply sumElim (doubletonPrimitive (Primrec.fst.comp Primrec.snd)
    (Primrec.snd.comp Primrec.snd))
  apply sumElim (Primrec.const [])
  apply sumElim (singletonPrimitive Primrec.snd)
  apply sumElim (doubletonPrimitive
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  exact sumElim (Primrec.const [])
    (doubletonPrimitive (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

theorem viewRootBoundsPrimitive (n : Nat) : Primrec (viewRootBounds n) := by
  unfold viewRootBounds
  apply sumElim (Primrec.const (1, 0))
  apply sumElim (Primrec.const (1, 0))
  apply sumElim (Primrec.const (1, 0))
  apply sumElim (Primrec.const (1, 0))
  apply sumElim (Primrec.const (1, 0))
  apply sumElim ((Primrec.const 1).pair Primrec.fst)
  exact sumElim (Primrec.const (0, 0)) (Primrec.const (0, 0))

theorem childrenPrimitive (n : Nat) : Primrec (@children (Fin n)) :=
  ((viewChildrenPrimitive n).comp (NumberedCodeViewProof.viewPrimitive n)).of_eq
    (by intro code; cases code <;> rfl)

theorem rootBoundsPrimitive (n : Nat) : Primrec (@rootBounds (Fin n)) :=
  ((viewRootBoundsPrimitive n).comp (NumberedCodeViewProof.viewPrimitive n)).of_eq
    (by intro code; cases code <;> rfl)

def mergeBounds (p : (Nat × Nat) × (Nat × Nat)) : Nat × Nat :=
  (p.1.1 + p.2.1, max p.1.2 p.2.2)

def collectBounds (values : List (Nat × Nat)) : Nat × Nat :=
  values.foldr (fun value rest => mergeBounds (value, rest)) (0, 0)

def recombine {Symbol : Type} (code : Code Symbol) (values : List (Nat × Nat)) :
    Option (Nat × Nat) :=
  some (mergeBounds (rootBounds code, collectBounds values))

theorem mergeBoundsPrimitive : Primrec mergeBounds :=
  (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
    (Primrec.nat_max.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))

theorem collectBoundsPrimitive : Primrec collectBounds := by
  unfold collectBounds
  exact Primrec.list_foldr Primrec.id (Primrec.const (0, 0))
    (mergeBoundsPrimitive.comp Primrec.snd).to₂

theorem recombinePrimitive (n : Nat) : Primrec₂ (@recombine (Fin n)) :=
  (Primrec.option_some.comp (mergeBoundsPrimitive.comp
    (((rootBoundsPrimitive n).comp Primrec.fst).pair
      (collectBoundsPrimitive.comp Primrec.snd)))).to₂

theorem childrenDecrease (n : Nat) (code child : Code (Fin n))
    (hchild : child ∈ children code) : codeNumber child < codeNumber code := by
  cases code with
  | var index => simp [children] at hchild
  | lam sigma body =>
    have he : child = body := by simpa [children] using hchild
    subst child
    have hp := Nat.add_le_pair 1 (Nat.pair (typeNumber sigma) (codeNumber body))
    have hb := Nat.right_le_pair (typeNumber sigma) (codeNumber body)
    change codeNumber body < Nat.pair 1 (Nat.pair (typeNumber sigma) (codeNumber body))
    omega
  | app sigma q a =>
    have he : child = q ∨ child = a := by simpa [children] using hchild
    have hp := Nat.add_le_pair 2
      (Nat.pair (typeNumber sigma) (Nat.pair (codeNumber q) (codeNumber a)))
    have hb := Nat.right_le_pair (typeNumber sigma)
      (Nat.pair (codeNumber q) (codeNumber a))
    have hc := Nat.add_le_pair (codeNumber q) (codeNumber a)
    change codeNumber child < Nat.pair 2
      (Nat.pair (typeNumber sigma) (Nat.pair (codeNumber q) (codeNumber a)))
    rcases he with rfl | rfl <;> omega
  | bottom tau => simp [children] at hchild
  | ordinary head base =>
    have he : child = base := by simpa [children] using hchild
    subst child
    have hp := Nat.add_le_pair 4 (Nat.pair (headNumber head) (codeNumber base))
    have hb := Nat.right_le_pair (headNumber head) (codeNumber base)
    change codeNumber base < Nat.pair 4 (Nat.pair (headNumber head) (codeNumber base))
    omega
  | numbered k head tau base types extras =>
    have he : child = base ∨ child = extras := by simpa [children] using hchild
    let p4 := Nat.pair (typesNumber types) (codeNumber extras)
    let p3 := Nat.pair (codeNumber base) p4
    let p2 := Nat.pair (typeNumber tau) p3
    let p1 := Nat.pair (headNumber head) p2
    let payload := Nat.pair k p1
    have hp := Nat.add_le_pair 5 payload
    have h1 := Nat.right_le_pair k p1
    have h2 := Nat.right_le_pair (headNumber head) p2
    have h3 := Nat.right_le_pair (typeNumber tau) p3
    have hb := Nat.add_le_pair (codeNumber base) p4
    have hextra := Nat.right_le_pair (typesNumber types) (codeNumber extras)
    change codeNumber child < Nat.pair 5 payload
    rcases he with rfl | rfl <;> omega
  | argumentsNil => simp [children] at hchild
  | argumentsCons tau q rest =>
    have he : child = q ∨ child = rest := by simpa [children] using hchild
    have hp := Nat.add_le_pair 7
      (Nat.pair (typeNumber tau) (Nat.pair (codeNumber q) (codeNumber rest)))
    have hb := Nat.right_le_pair (typeNumber tau)
      (Nat.pair (codeNumber q) (codeNumber rest))
    have hc := Nat.add_le_pair (codeNumber q) (codeNumber rest)
    change codeNumber child < Nat.pair 7
      (Nat.pair (typeNumber tau) (Nat.pair (codeNumber q) (codeNumber rest)))
    rcases he with rfl | rfl <;> omega

theorem recombineCalibration {Symbol : Type} (code : Code Symbol) :
    recombine code ((children code).map codeBounds) = some (codeBounds code) := by
  cases code <;> simp [recombine, children, rootBounds, collectBounds, mergeBounds,
    codeBounds, Nat.add_assoc]

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSyntaxBoundsPrimrecSupportProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSyntaxBoundsPrimrecSupportProof
