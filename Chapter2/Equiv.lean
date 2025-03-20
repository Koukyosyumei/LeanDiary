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
inductive ceval : Command -> State -> State -> Prop
| E_Skip : ∀ (st : State),
    ceval Command.skip st st
| E_Assign : ∀ (st : State) (x : String) (n : ℕ),
    ceval (Command.assign x n) st (set st x n)
| E_AssignVar : ∀ (st : State) (x : String) (y : String),
    ceval (Command.assignvar x y) st (set st x (get st y))
| E_Seq : ∀ (c1 c2 : Command) (st st' st'' : State),
    ceval c1 st st' →
    ceval c2 st' st'' →
    ceval (Command.seq c1 c2) st st''
| E_IfTrue : ∀ (st st' : State) (b : Bool) (c1 c2 : Command),
    b = true → ceval c1 st st' → ceval (Command.if_ b c1 c2) st st'
| E_IfFalse : ∀ (st st' : State) (b : Bool) (c1 c2 : Command),
    b = false → ceval c2 st st' → ceval (Command.if_ b c1 c2) st st'
| E_WhileFalse : ∀ (st : State) (b : Bool) (c : Command),
    b = false → ceval (Command.while b c) st st
| E_WhileTrue : ∀ (st st' st'' : State) (b : Bool) (c : Command),
    b = true → ceval c st st' → ceval (Command.while b c) st' st'' → ceval (Command.while b c) st st''

namespace Equiv

def cequiv (c₁ c₂ : Command) : Prop :=
    ∀ (st st' : State),
    ceval c₁ st st' ↔ ceval c₂ st st'

-- Executing `skip` does not change the State
-- This directly follows from the `E_Skip` rule
theorem skip_preserves_State:
  ∀ (st: State), ceval Command.skip st st := by
  apply ceval.E_Skip

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
    -- Since `h` is a proof about a sequence evaluation, it must have been constructed using the `E_Seq` rule.
    -- This breaks `h` down into its components.
    cases h
    -- This pattern matches the `E_Seq` constructor, giving us:
    --     `st''`: An intermediate State after executing skip
    --     `h_skip`: A proof that `ceval Command.skip st st''`
    --     `h_c`: A proof that `ceval c st'' st'`
    case E_Seq st'' h_skip h_c =>
        cases h_skip
        -- Matches the `E_Skip` constructor
        case E_Skip =>
            exact h_c
  -- backward (←)
  . intro h
    apply ceval.E_Seq
    . apply ceval.E_Skip
    . exact h

theorem skip_right:
    ∀ (c: Command), cequiv (Command.seq c Command.skip) c := by
    intro c
    rw[cequiv]
    intros st st'
    constructor
    . intro h
      cases h
      case E_Seq st'' h_c h_skip =>
        cases h_skip
        case E_Skip =>
            exact h_c
    . intro h
      apply ceval.E_Seq
      . exact h
      . apply ceval.E_Skip

theorem if_true:
    ∀ (b: Bool), ∀ (c₁ c₂ : Command), b = true → cequiv (Command.if_ b c₁ c₂) c₁ := by
    intros b c₁ c₂ htrue
    rw[cequiv]
    intros st st'
    constructor
    . intro h
      cases h
      case E_IfTrue _ hc =>
        exact hc
      case E_IfFalse hfalse hc =>
        rw[htrue] at hfalse
        contradiction
    . intro h
      apply ceval.E_IfTrue
      . rw[htrue]
      . exact h

theorem if_false:
    ∀ (b: Bool), ∀ (c₁ c₂ : Command), b = false → cequiv (Command.if_ b c₁ c₂) c₂ := by
    intros b c₁ c₂ hfalse
    rw[cequiv]
    intros st st'
    constructor
    . intro h
      cases h
      case E_IfTrue htrue hc =>
        rw[hfalse] at htrue
        contradiction
      case E_IfFalse _ hc =>
        exact hc
    . intro h
      apply ceval.E_IfFalse
      . rw[hfalse]
      . exact h

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
      case E_WhileFalse _ =>
        apply ceval.E_Skip
      case E_WhileTrue htrue hc hw =>
        rw[hfalse] at htrue
        contradiction
    . intro h
      cases h
      case E_Skip =>
        apply ceval.E_WhileFalse
        exact hfalse

theorem seq_assoc:
    ∀ (c₁ c₂ c₃ : Command), cequiv (Command.seq (Command.seq c₁ c₂) c₃) (Command.seq c₁ (Command.seq c₂ c₃)) := by
    intros c₁ c₂ c₃
    rw[cequiv]
    intros st st'
    constructor
    . intro h
      cases h
      case E_Seq st'' hs hc =>
        cases hs
        case E_Seq st1 h1 h2 =>
            apply ceval.E_Seq
            . exact h1
            apply ceval.E_Seq
            . exact h2
            . exact hc
    . intro h
      cases h
      case E_Seq st'' hs hc =>
        cases hc
        case E_Seq st1 h1 h2 =>
            apply ceval.E_Seq
            apply ceval.E_Seq
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
