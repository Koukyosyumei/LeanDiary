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

notation p " [" x " ↦ " a "]" => assertion_sub p x a

example (x : String):
  assertion_sub (fun st => st x ≤ 5) x (Imp.AExp.const 3) <<->> (fun _ => 3 ≤ 5) := by
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

theorem hoare_asgn : ∀ (q : Assertion) (x : String) (a : Imp.AExp),
  valid_hoare_triple (assertion_sub q x a) (Imp.Command.assign x a) q := by
  intros q x a
  unfold valid_hoare_triple
  intros st₁ st₂ ha hb
  unfold assertion_sub at hb
  cases ha
  case assign n₁ ha₁ =>
    apply hb
    exact ha₁

example (x : String):
  valid_hoare_triple (assertion_sub (fun st => st x < 5) x (.add (.var x) (.const 1))) (.assign x (.add (.var x) (.const 1))) (fun st => st x < 5) := by
  apply hoare_asgn

example (x: String):
  ∃ (p : Assertion), valid_hoare_triple p (.assign x (.mul (.const 2) (.var x))) (fun st => st x ≤ 10) := by
  exists assertion_sub (fun st => st x ≤ 10) x (.mul (.const 2) (.var x))
  apply hoare_asgn

example (x: String):
  ∃ (p : Assertion), valid_hoare_triple p (.assign x (.const 3)) (fun st => 0 ≤ (st x) ∧ (st x) ≤ 5) := by
  exists assertion_sub (fun st => 0 ≤ st x ∧ st x ≤ 5) x (Imp.AExp.const 3)
  apply hoare_asgn

theorem hoare_asgn_wrong (x : String) : ∃ (a : Imp.AExp),
  ¬ valid_hoare_triple (fun st => true) (.assign x a) (fun st => Imp.AEval st a (st x)) := by
  exists (.add (.var x) (.const 1))
  unfold valid_hoare_triple
  intros h
  simp_all
  let st₁ : Imp.State := fun y => if y = x then 0 else 0
  let st₂ := Imp.set st₁ x (st₁ x + 1)
  specialize h st₁ st₂
  have ha : (st₁ ⊢ Imp.Command.assign x ((Imp.AExp.var x).add (Imp.AExp.const 1)) ⇓ st₂) := by
    {
      apply Imp.CEval.assign
      apply Imp.AEval.add
      apply Imp.AEval.var
      apply Imp.AEval.const
    }
  apply h at ha
  simp_all
  have h₁ : st₂ x = st₁ x := by
    {
      sorry
    }
  have contra : st₂ x = (st₁ x) + 1 := by
    {
      sorry
    }
  rw[h₁] at contra
  let n : ℕ := st₁ x
  have hn : n = st₁ x := by rfl
  rw[← hn] at contra
  simp_all

end Hoare1
