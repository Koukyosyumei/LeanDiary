import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

-- A `State` can be modeled as a function mapping variable names
-- to values (e.g., natural numbers in this tutorial)
def State := String -> ℕ

-- Retrive the value of a variable in the State
def get (st: State) (x : String) : ℕ := st x

-- Update the State with a new value for a variable
def set (st: State) (x : String) (v: ℕ) : State :=
  fun y => if y = x then v else st y

-- Syntax of commands
inductive Command: Type
| skip: Command                               -- nop
| assign (x : String) (a: ℕ) : Command        -- x := a
| assignvar (x: String) (y: String) : Command -- x := y
| seq (c1 c2 : Command) : Command                 -- c1; c2
| if_ (b : Bool) (c1 c2 : Command) : Command      -- if b then c1 else c2
| while (b : Bool) (c : Command) : Command        -- while b do c

-- inductive definitions in Lean come with an important implicit principle:
-- ** the only ways to construct proofs of the inductive relation are through its constructors.

-- State transition
inductive CEval : Command -> State -> State -> Prop
| skip (st : State) :
    CEval .skip st st
| assign (st : State) (x : String) (n : ℕ) :
    CEval (.assign x n) st (set st x n)
| assignvar (st : State) (x : String) (y : String) :
    CEval (.assignvar x y) st (set st x (get st y))
| seq (c1 c2 : Command) (st st' st'' : State) :
    CEval c1 st st' → CEval c2 st' st'' → CEval (.seq c1 c2) st st''
| if_true (st st' : State) (c1 c2 : Command) :
    CEval c1 st st' → CEval (.if_ true c1 c2) st st'
| if_false (st st' : State) (b : Bool) (c1 c2 : Command) :
    CEval c2 st st' → CEval (.if_ false c1 c2) st st'
| while_false : ∀ (st : State) (b : Bool) (c : Command),
    b = false → CEval (Command.while b c) st st
| while_true : ∀ (st st' st'' : State) (b : Bool) (c : Command),
    b = true → CEval c st st' → CEval (Command.while b c) st' st'' → CEval (Command.while b c) st st''

namespace Equiv

def cequiv (c₁ c₂ : Command) : Prop :=
    ∀ (st st' : State),
    CEval c₁ st st' ↔ CEval c₂ st st'

-- Executing `skip` does not change the State
-- This directly follows from the `skip` rule
theorem skip_preserves_State:
  ∀ (st: State), CEval Command.skip st st := by
  apply CEval.skip

-- Proving a command equivalence

-- ∀c, (skip; c) is equivalent to c
theorem skip_left:
  ∀ (c: Command), cequiv (Command.seq Command.skip c) c := by
  intro c
  -- breaking the Statement into two directions
  rw [cequiv]
  intros st st'
  constructor
  -- forward (→)
  . intro h
    -- Since `h` is a proof about a sequence evaluation, it must have been constructed using the `seq` rule.
    -- This breaks `h` down into its components.
    cases h
    -- This pattern matches the `seq` constructor, giving us:
    --     `st''`: An intermediate State after executing skip
    --     `h_skip`: A proof that `CEval Command.skip st st''`
    --     `h_c`: A proof that `CEval c st'' st'`
    case seq st'' h_skip h_c =>
        cases h_skip
        -- Matches the `skip` constructor
        case skip =>
            exact h_c
  -- backward (←)
  . intro h
    apply CEval.seq
    . apply CEval.skip
    . exact h

theorem skip_right:
    ∀ (c: Command), cequiv (Command.seq c Command.skip) c := by
    intro c
    rw[cequiv]
    intros st st'
    constructor
    . intro h
      cases h
      case seq st'' h_c h_skip =>
        cases h_skip
        case skip =>
            exact h_c
    . intro h
      apply CEval.seq
      . exact h
      . apply CEval.skip

theorem if_true:
    ∀ (b: Bool), ∀ (c₁ c₂ : Command), b = true → cequiv (Command.if_ b c₁ c₂) c₁ := by
    intros b c₁ c₂ htrue
    rw[cequiv]
    intros st st'
    constructor
    . intro h
      cases h
      case if_true hc =>
        exact hc
      case if_false hfalse hc =>
        contradiction
    . intro h
      rw[htrue]
      apply CEval.if_true
      exact h

theorem if_false:
    ∀ (b: Bool), ∀ (c₁ c₂ : Command), b = false → cequiv (Command.if_ b c₁ c₂) c₂ := by
    intros b c₁ c₂ hfalse
    rw[cequiv]
    intros st st'
    constructor
    . intro h
      cases h
      case if_true hc =>
        contradiction
      case if_false _ hc =>
        exact hc
    . intro h
      rw[hfalse]
      apply CEval.if_false
      exact b
      exact h


theorem swap_if_branches:
    ∀ (b : Bool), ∀ (c₁ c₂ : Command), cequiv (Command.if_ b c₁ c₂) (Command.if_ (¬b) c₂ c₁) := by
    intros b c₁ c₂
    rw[cequiv]
    intros st st'
    constructor
    . intro h
      cases b
      case false =>
        rw[if_true]
        rw[if_false] at h
        exact h
        repeat rfl
      case true =>
        rw[if_false]
        rw[if_true] at h
        exact h
        repeat rfl
    . intro h
      cases b
      case false =>
        rw[if_false]
        rw[if_true] at h
        exact h
        repeat rfl
      case true =>
        rw[if_true]
        rw[if_false] at h
        exact h
        repeat rfl

theorem while_false:
    ∀ (b : Bool), ∀ (c : Command), b = false → cequiv (Command.while b c) Command.skip := by
    intros b c₁ hfalse
    rw[cequiv]
    intros st st'
    constructor
    . intro h
      cases h
      case while_false _ =>
        apply CEval.skip
      case while_true htrue hc hw =>
        rw[hfalse] at htrue
        contradiction
    . intro h
      cases h
      case skip =>
        apply CEval.while_false
        exact hfalse

theorem seq_assoc:
    ∀ (c₁ c₂ c₃ : Command), cequiv (Command.seq (Command.seq c₁ c₂) c₃) (Command.seq c₁ (Command.seq c₂ c₃)) := by
    intros c₁ c₂ c₃
    rw[cequiv]
    intros st st'
    constructor
    . intro h
      cases h
      case seq st'' hs hc =>
        cases hs
        case seq st1 h1 h2 =>
            apply CEval.seq
            . exact h1
            apply CEval.seq
            . exact h2
            . exact hc
    . intro h
      cases h
      case seq st'' hs hc =>
        cases hc
        case seq st1 h1 h2 =>
            apply CEval.seq
            apply CEval.seq
            .exact hs
            .exact h1
            .exact h2

lemma h_eq (st: State) (x : String) : set st x (get st x) = st := by
    funext y
    unfold _root_.set _root_.get
    by_cases h: y = x
    {
        rw[if_pos h]
        rw[h]
    }
    {
        rw[if_neg h]
    }


end Equiv
