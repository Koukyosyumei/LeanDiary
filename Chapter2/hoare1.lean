import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Chapter2.Imp

namespace Hoare1

def Assertion := Imp.State -> Prop

-- Examples
def assertion1 (x y : String): Assertion := fun st => st x ≤ st y
def assertion2 (x y : String): Assertion := fun st => st x = 3 ∨ st x ≤ st y

def assert_implies (p q : Assertion): Prop := ∀ st, p st → q st
def assert_iff (p q : Assertion): Prop := ∀ st, (p st → q st) ∧ (q st → p st)

def valid_hoare_triple (p : Assertion) (c : Imp.Command) (q: Assertion): Prop :=
  ∀ (st₁ st₂ : Imp.State), Imp.CEval st₁ c st₂ → p st₁ → q st₂

notation p " ->> " q  => assert_implies p q
notation p " <<->> " q => assert_iff p q
notation "{" p "} " c " {" q "}" => valid_hoare_triple p c q

-- If q holds in every state, then any triple with q as its precondition is valid.
theorem hoare_post_true : ∀ (p q : Assertion) (c : Imp.Command),
  (∀ (st : Imp.State), q st) → valid_hoare_triple p c q := by
  intros p q c hq_st
  unfold valid_hoare_triple
  intros st₁ st₂ hc hp
  apply hq_st st₂

-- if p holds in no state, then any triple with p as its precondition is valid
theorem hoare_pre_false : ∀ (p q : Assertion) (c : Imp.Command),
  (∀ (st : Imp.State), ¬(p st)) → valid_hoare_triple p c q := by
  intros p q c hq_st
  unfold valid_hoare_triple
  intros st₁ st₂ hc hp
  apply hq_st st₁ at hp
  contradiction

theorem hoare_skip : ∀ (p : Assertion), valid_hoare_triple p Imp.Command.skip p := by
  intro p
  unfold valid_hoare_triple
  intros st₁ st₂ hc hp
  cases hc
  case skip =>
    exact hp

theorem hoare_seq : ∀ (p q r : Assertion), ∀ (c₁ c₂ : Imp.Command),
  valid_hoare_triple q c₂ r → valid_hoare_triple p c₁ q → valid_hoare_triple p (Imp.Command.seq c₁ c₂) r := by
  intros p q r c₁ c₂ hc₂ hc₁
  unfold valid_hoare_triple
  unfold valid_hoare_triple at hc₁
  unfold valid_hoare_triple at hc₂
  intros st₁ st₂ hc hp
  cases hc
  case seq st₃ hs₁ hs₂ =>
    apply hc₁ at hs₁
    apply hc₂ at hs₂
    apply hs₁ at hp
    apply hs₂ at hp
    exact hp

def assertion_sub (p : Assertion) (x : String) (a : Imp.AExp) : Assertion :=
  fun st => ∀ n, Imp.AEval st a n → p (Imp.set st x n)

notation p " [" x " → " a "]" => assertion_sub p x a

example (x : String):
  assertion_sub (fun st => st x ≤ 5) x (Imp.AExp.const 3) <<->> (fun st => 3 ≤ 5) := by
  unfold assert_iff
  intros st
  constructor
  . intro ha
    simp_all
  . intro ha
    unfold assertion_sub
    intros n he
    cases he
    case right.const =>
      unfold Imp.set
      simp_all

example (x : String):
  assertion_sub (fun st => st x ≤ 5) x (.add (.var x) (.const 1)) <<->> (fun st => (st x ) + 1 ≤ 5) := by
  unfold assert_iff
  unfold assertion_sub
  intro st
  constructor
  . intro ha
    specialize ha (st x + 1)
    unfold Imp.set at ha
    simp_all
    apply ha
    apply Imp.AEval.add
    apply Imp.AEval.var
    apply Imp.AEval.const
  . intro ha n hb
    unfold Imp.set
    simp_all
    cases hb
    case right.add n₁ n₂ ha₁ ha₂ =>
      cases ha₂
      case const =>
        simp_all
        cases ha₁
        case var =>
          unfold Imp.get
          exact ha





end Hoare1
